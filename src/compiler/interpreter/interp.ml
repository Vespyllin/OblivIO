module T = Thread
module M = Common.Message
module L = Common.Level
module A = Common.Tabsyn
module V = Common.Value
module Ty = Common.Types
module Tr = Common.Trace
module C = Common.Channel

module H = Hashtbl

open Common.Value
open Common.Oper

type handler_info = {x: string; body: A.cmd}
type server_info = {input: in_channel; output: out_channel}

type 'a sync_queue =
  { lock: Mutex.t
  ; queue: 'a Queue.t
  }

type context = 
  { name: string
  ; unsafe: bool
  ; message_queue: M.message sync_queue
  ; mutable input_buffer: char array
  ; memory: (string, value) H.t
  ; store: (string, value) H.t
  ; heap: (int, value) H.t
  ; mutable next_address: int
  ; handlers: (string, handler_info) H.t
  ; trust_map: (C.channel, L.level * Ty.ty) H.t
  ; server: server_info
  ; trace: Tr.trace
  }

let enqueue (msg: 'a) (q: 'a sync_queue) =
  Mutex.lock q.lock;
  Queue.add msg q.queue;
  Mutex.unlock q.lock

let dequeue (q: 'a sync_queue) =
  Mutex.lock q.lock;
  let msg_opt = Queue.take_opt q.queue in
  Mutex.unlock q.lock;
  msg_opt

let send ctxt msg = 
  output_value ctxt.server.output msg;
  flush ctxt.server.output;
  match msg with
  | M.Relay _ ->
    Tr.add_send (Sys.time()) msg ctxt.trace
  | _ -> ()

exception InterpFatal of string
exception NotImplemented of string
  
let lookup m x =
  match H.find_opt m x with
  | Some v -> v
  | None -> raise @@ InterpFatal ("lookup")

let safeDiv a b =
  let b0 = Bool.to_int (b = 0) in
  let b' = b*(b0 lxor 1) lor b0 in
  ((a / b')*(b0 lxor 1)) lor (b0*max_int)

let _int = function
  | IntVal n -> n
  | _ -> raise @@ InterpFatal "_I"

let _string = function
  | StringVal{data;_} -> data |> Array.to_seq |> String.of_seq
  | _ -> raise @@ InterpFatal "_I"

(* TODO: THIS IS WRONG! NOT GUARANTEED TO HAVE ZEROED OUT CHAR ARRAY! *)
let safeConcat l (arr1 : char array) (arr2 : char array) =
  let l1 = Array.length arr1 in
  let l2 = Array.length arr2 in
  let len = l1 + l2 in
  let res = Array.make len '\000' in
  let c = ref 0 in
  for i = 0 to len-1 do
    for j = 0 to l1-1 do
      let v = Char.code @@ arr1.(j) in
      let b = Bool.to_int (i = j) land Bool.to_int (j < l) in
      c := !c lor (v*b)
    done;
    for j = 0 to l2-1 do
      let v = Char.code @@ arr2.(j) in
      let b = Bool.to_int (i = j+l) in
      c := !c lor (v*b)
    done;
    res.(i) <- Char.chr !c;
    c := 0
  done;
  res

let rec safeEq v1 v2 =
  match v1, v2 with
  | IntVal a, IntVal b -> 
    Bool.to_int @@ (a lxor b = 0)
  | StringVal{length=l1;data=d1}, StringVal{length=l2;data=d2} ->
    let mismatch = ref (l1 lxor l2) in
    let publen = min (Array.length d1) (Array.length d2) in
    let seclen = min l1 l2 in
    for i = 0 to publen-1 do
      let bit = Bool.to_int(i < seclen) in
      let i1 = Char.code @@ d1.(i) in
      let i2 = Char.code @@ d2.(i) in
      mismatch := (bit land (i1 lxor i2)) lor !mismatch
    done;
    Bool.to_int (!mismatch = 0)
  | PairVal(a1,a2), PairVal (b1,b2) ->
    safeEq a1 b1 * safeEq a2 b2
  | ArrayVal{length=l1;data=d1;_}, ArrayVal{length=l2;data=d2;_} ->
    let mismatch = ref (l1 lxor l2) in
    let publen = min (Array.length d1) (Array.length d2) in
    let seclen = min l1 l2 in
    for i = 0 to publen-1 do
      let bit = Bool.to_int(i < seclen) in
      let i = safeEq d1.(i) d2.(i) in
      mismatch := (bit land (1 lxor i)) lor !mismatch
    done;
    Bool.to_int (!mismatch = 0)
  | _ -> raise @@ NotImplemented "safeEq"

exception Unequal
let rec unsafeEq v1 v2 =
  match v1, v2 with
  | IntVal a, IntVal b -> 
    Bool.to_int @@ (a = b)
  | StringVal{length=l1;data=d1}, StringVal{length=l2;data=d2} ->
    begin
    try
      if l1 <> l2 then raise Unequal;
      for i = 0 to (min l1 l2)-1 do
        if d1.(i) <> d2.(i) then raise Unequal
      done;
      1
    with Unequal -> 0
    end
  | PairVal(a1,a2), PairVal (b1,b2) ->
    unsafeEq a1 b1 * safeEq a2 b2
  | ArrayVal{length=l1;data=d1;_}, ArrayVal{length=l2;data=d2;_} ->
    begin
    try
      if l1 <> l2 then raise Unequal;
      for i = 0 to (min l1 l2)-1 do
        let i = unsafeEq d1.(i) d2.(i) in
        if (i = 0) then raise Unequal
      done;
      1
    with Unequal -> 0
    end
  | _ -> raise @@ NotImplemented "unsafeEq"

let safeSelect (bit: int) (orig: value) (upd: value) =
  let rec _S orig upd =
    match orig, upd with
    | IntVal a, IntVal b ->
      IntVal (((bit lxor 1) * a) lor (bit * b))
    | StringVal{length=l1;data=d1}, StringVal{length=l2;data=d2} ->
      begin
      match Array.length d1, Array.length d2 with
      | arrlen1, arrlen2 when arrlen1 < arrlen2 ->
        let length = ((1 lxor bit)*l1) lor (bit*l2) in
        let data = Array.copy d2 in
        for i = 0 to arrlen1-1 do
          let i1 = (1 lxor bit) * (Char.code @@ d1.(i)) in
          let i2 = bit * (Char.code @@ d2.(i)) in
          data.(i) <- Char.chr @@ i1 lor i2
        done;
        StringVal{length;data}
      | _, arrlen2 ->
        let length = ((1 lxor bit)*l1) lor (bit*l2) in
        let data = Array.copy d1 in
        for i = 0 to arrlen2-1 do
          let i1 = (1 lxor bit) * (Char.code @@ d1.(i)) in
          let i2 = bit * (Char.code @@ d2.(i)) in
          data.(i) <- Char.chr @@ i1 lor i2
        done;
        StringVal{length;data}
      end
    | PairVal (a1,a2), PairVal (b1,b2) ->
      PairVal (_S a1 b1, _S a2 b2)
    | ArrayVal{length=_l1;data=d1}, ArrayVal{length=_l2;data=d2} ->
      begin
        (* TOOD: make oblivious *)
        match Array.length d1, Array.length d2 with
        | arrlen1, arrlen2 when arrlen1 <= arrlen2 ->
          (* let length = ((1 lxor bit)*l1) lor (bit*l2) in
          let data = Array.copy d2 in *)
          if bit = 1 then upd else orig
          (* raise @@ InterpFatal "Safeselect arr" *)
          (* for i = 0 to arrlen1-1 do *)
            (* data.(i) <- _S d1.(i) d2.(i) *)
          (* done; *)
          (* ArrayVal{length;data} *)
        | _, _arrlen2 ->
          if bit = 1 then upd else orig
          (* let length = ((1 lxor bit)*l1) lor (bit*l2) in
          let data = Array.copy d1 in
          for i = 0 to arrlen2-1 do
            data.(i) <- safeSelect bit d1.(i) d2.(i)
          done;
          ArrayVal{length;data} *)
          (* raise @@ InterpFatal "Safeselect arr" *)
      end
    | _ -> raise @@ InterpFatal ("safeSelect: " ^ (V.to_string orig) ^  ", " ^ (V.to_string upd)) in
  _S orig upd

let op oper v1 v2 =
  match oper,v1,v2 with
  (* POLY *)
  | EqOp, _, _ ->
    IntVal (safeEq v1 v2)
  | NeqOp, _, _ ->
    IntVal ((safeEq v1 v2) lxor 1)
  (* INT *)
  | LtOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a - b < 0))
  | LeOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a - b <= 0))
  | GtOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a - b > 0))
  | GeOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a - b >= 0))
  | AndOp, IntVal a, IntVal b ->
    let ai = (Bool.to_int @@ (a <> 0)) in
    let bi = (Bool.to_int @@ (b <> 0)) in
    IntVal (Bool.to_int @@ (ai land bi > 0))
  | OrOp, IntVal a, IntVal b ->
    let ai = (Bool.to_int @@ (a <> 0)) in
    let bi = (Bool.to_int @@ (b <> 0)) in
    IntVal (Bool.to_int @@ (ai lor bi > 0))
  | PlusOp, IntVal a, IntVal b ->
    IntVal (a+b)
  | MinusOp, IntVal a, IntVal b ->
    IntVal (a-b)
  | TimesOp, IntVal a, IntVal b ->
    IntVal (a*b)
  (* STRING *)
  (* TODO: ERROR SIZING *)
  | CaretOp, StringVal {length=l1;data=d1}, StringVal {length=l2;data=d2} ->
    StringVal {length=l1+l2; data=safeConcat l1 d1 d2}
    (* TODO: look into the first param of safeConcat *)
  | CaretOp, ErrVal {padding=e1;_}, StringVal {data=d2;_} ->
    ErrVal {padding=(safeConcat (Array.length e1) e1 d2); elem_size=0}
  | CaretOp, StringVal {length=l1;data=d1}, ErrVal {padding=e2;_} ->
    ErrVal {padding=(safeConcat l1 d1 e2);elem_size=0}
  (* ARRAY *)
  (* | CaretOp, ArrayVal {length=l1;data=d1}, ArrayVal {length=l2;data=d2} -> *)
    (* ArrayVal {length=l1+l2; data=(safeConcatArr l1 d1 d2)} *)
  (* | CaretOp, ErrVal e1, ArrayVal {length=l2;data=d2;elem_size} ->
    ErrVal (Array.append e1 (Array.make l2 '\000'))
  | CaretOp, ArrayVal {length=l1;data=d1;elem_size}, ErrVal e2 ->
    ErrVal (Array.append (Array.make l1 '\000') e2)
  | CaretOp, ErrVal e1, ErrVal e2 ->
    ErrVal (Array.append e1 e2) *)
  
  (* COALESCE *)
  | CoalesceOp, ErrVal {padding=e1;elem_size=elem_size1}, ErrVal {padding=e2;elem_size=elem_size2} ->
    let maxlen = max (Array.length e1) (Array.length e2) in
    ErrVal {padding=(Array.make maxlen '\000'); elem_size=max elem_size1 elem_size2}
  | CoalesceOp, ErrVal _, b -> b
  | CoalesceOp, a, _ -> a
  (* ERROR INT *)
  | _, ErrVal _, _  
  | _, _, ErrVal _ -> 
    ErrVal{padding=[||]; elem_size=0}
  | _ -> raise @@ NotImplemented (V.to_string v1 ^ to_string oper ^ V.to_string v2)

let op_unsafe oper v1 v2 =
  match oper,v1,v2 with
  (* POLY *)
  | EqOp, _, _ ->
    IntVal (unsafeEq v1 v2)
  | NeqOp, _, _ ->
    IntVal ((unsafeEq v1 v2) lxor 1)
  (* INT *)
  | LtOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a < b))
  | LeOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a <= b))
  | GtOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a > b))
  | GeOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a >= b))
  | AndOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a <> 0 && b <> 0))
  | OrOp, IntVal a, IntVal b ->
    IntVal (Bool.to_int @@ (a <> 0 || b <> 0))
  | PlusOp, IntVal a, IntVal b ->
    IntVal (a+b)
  | MinusOp, IntVal a, IntVal b ->
    IntVal (a-b)
  | TimesOp, IntVal a, IntVal b ->
    IntVal (a*b)
  (* STRING *)
  | CaretOp, StringVal {length=l1;data=d1}, StringVal {length=l2;data=d2} ->
    let d1' = Array.sub d1 0 l1 in
    let d2' = Array.sub d2 0 l2 in
    StringVal {length=l1+l2; data=Array.append d1' d2'}

    (* TODO: error sizing *)
  | CaretOp, ErrVal {padding=e1;_}, StringVal {data=d2;_} -> 
    ErrVal {padding=(Array.append e1 d2); elem_size=0}
  | CaretOp, StringVal {data=d1;_}, ErrVal {padding=e2;_} -> 
    ErrVal {padding=(Array.append d1 e2); elem_size=0}

  | CoalesceOp, ErrVal _, b -> b
  | CoalesceOp, a, _ -> a
  | _, ErrVal _, _  
  | _, _, ErrVal _ -> 
    ErrVal{padding= [||]; elem_size=0}
  | _ -> raise @@ NotImplemented (V.to_string v1 ^ to_string oper ^ V.to_string v2)

type update = ASSIGN | BIND
let rec readvar ctxt =
  let rec _V access_path (A.Var{var_base;loc;_}) = match var_base with
    | A.SimpleVar x ->
      let v = 
        match loc with
        | LOCAL -> lookup ctxt.memory x
        | STORE -> lookup ctxt.store x in
      let rec unwrap_indices access_elem v =
        match access_elem, v with
        | [], _ -> v
        | (idx,lvl)::idx_tl, ArrayVal{length;data;_} ->
          (* TODO: inherit elem size from parent array *)
          let maxidx = length - 1 in
          let cnd1 = Bool.to_int(idx >= 0) in
          let cnd2 = Bool.to_int(idx > maxidx) in
          let idx = cnd1 * idx in
          let idx = ((cnd2 lxor 1) * idx) lor (cnd2 * maxidx) in
          let res =
            if L.flows_to lvl L.bottom || ctxt.unsafe
              then if idx > maxidx then
                (* TODO: OBLIVIATE *)
                raise @@ InterpFatal "out of bounds"
              else
                unwrap_indices idx_tl data.(idx)
            else 
              let len = Array.length data - 1 in
              let res = unwrap_indices idx_tl data.(0) in
              let a = ref res in
              for i = 0 to len do
                let b = unwrap_indices idx_tl data.(i) in
                a := safeSelect (Bool.to_int (i lxor idx = 0)) !a b
              done;
              !a in  
            res
        | _ -> raise @@ InterpFatal "readVar"
        in
      unwrap_indices access_path v
    | A.SubscriptVar {var;exp} ->
      let A.Exp{ty;_} = exp in
      let i = _int @@ eval ctxt exp in
      let lvl = Ty.level ty in
      _V ((i,lvl)::access_path) var
    | A.HeapVar {var} ->
      let ptr = _V access_path var in
      let addr = match ptr with
        | PointerVal{addr; _} -> addr
        | _ -> raise @@ InterpFatal "HeapVar: not a pointer" in
      match H.find_opt ctxt.heap addr with
        | Some v -> v
        | None -> raise @@ InterpFatal ("could not find pointer in heap")
in _V []

and writevar ctxt updkind upd mode =
  let rec _V path (A.Var{var_base;_}) = match var_base with
    | A.SimpleVar x ->
      let v = lookup ctxt.store x in
      let rec f path v mode =
        match path, v with
        | [], _ ->
          begin 
          match updkind, ctxt.unsafe with
          | BIND, false ->
            let orig = lookup ctxt.store x in
            H.add ctxt.store x @@ safeSelect mode orig upd
          | _ -> if mode = 1 then 
            H.add ctxt.store x upd
          end
        | [(i,lvl)], ArrayVal{length;data; _} ->
          let maxidx = length -1 in
          let cnd1 = Bool.to_int(i >= 0) in
          let cnd2 = Bool.to_int(i > maxidx) in
          let idx = cnd1 * i in
          let idx = ((cnd2 lxor 1) * idx) lor (cnd2 * maxidx) in
          if L.flows_to lvl L.bottom || ctxt.unsafe
          then (* public index, no problem! *)
            match updkind, ctxt.unsafe with
            | BIND, false ->
              data.(idx) <- safeSelect mode data.(idx) upd
            | _ ->
              (* TODO: careful in case of array overwrite *)
              if mode = 1 then data.(idx) <- upd;
          else 
            (* non-public index, must obliv everything! *)
            let len = Array.length data - 1 in
            for i = 0 to len do
              let right_index = Bool.to_int (i lxor idx = 0) in
              data.(i) <- safeSelect (right_index land mode) data.(i) upd
            done          
        | (i,lvl)::tl, ArrayVal{length;data; _} ->
          let maxidx = length -1 in
          let cnd1 = Bool.to_int(i >= 0) in
          let cnd2 = Bool.to_int(i > maxidx) in
          let idx = cnd1 * i in
          let idx = ((cnd2 lxor 1) * idx) lor (cnd2 * maxidx) in
          if L.flows_to lvl L.bottom || ctxt.unsafe
          then f tl data.(idx) mode (* public index, no problem! *)
          else 
            (* non-public index, must obliv everything! *)
            let len = Array.length data - 1 in
            for i = 0 to len do
              let right_index = Bool.to_int (i lxor idx = 0) in
              f tl data.(i) (right_index land mode)
            done          
        | _ -> raise @@ InterpFatal "writeVar"
        in
      f path v mode
    | A.SubscriptVar {var;exp} ->
      let A.Exp{ty;_} = exp in
      let i = _int @@ eval ctxt exp in
      let lvl = Ty.level ty in
      _V ((i,lvl)::path) var
    | A.HeapVar {var} ->
      let ptr = readvar ctxt var in
      let addr, cell_size = match ptr with
        | PointerVal {addr; cell_size} -> addr, cell_size
        | _ -> raise @@ InterpFatal "HeapVar: not a pointer" in
      
      if addr = -1 
      then raise @@ InterpFatal "HeapVar: Attempting to write to null pointer";

      if V.size upd > cell_size
      then raise @@ InterpFatal "HeapVar: value exceeds cell_size";
      H.replace ctxt.heap addr upd
      
in _V []

(* TODO: safeSelect int, string, pair, ptr *)
and sizeSafeSelectWithDefault (v: value) (default: value) (mode: int) =
  match v, default with
  | IntVal _, IntVal _ ->
      if mode = 1 then v else default

  | StringVal {data=_da; length=_la}, StringVal {data=_db; length=_lb} ->
      if mode = 1 then v else default

  | ArrayVal _, ArrayVal _ ->
      if mode = 1 then v else default

  | PairVal _, PairVal _ ->
      if mode = 1 then v else default

  | PointerVal _, PointerVal _ ->
      if mode = 1 then v else default

  | ErrVal _, ErrVal _ ->
      if mode = 1 then v else default

  | _, _ ->
      raise @@ InterpFatal "sizeSafeSelect mismatched values"

and eval ctxt =
  let rec _E (A.Exp{exp_base;_}) =
    match exp_base with
    | A.IntExp i -> IntVal i
    | A.StringExp s -> 
      let length = String.length s in
      let data = s |> String.to_seq |> Array.of_seq in
      StringVal {length;data}
    | A.VarExp v -> 
      readvar ctxt v
    | A.ProjExp {proj;exp} ->
      let v = _E exp in
      begin
        match proj,v with
        | A.Fst, PairVal (a,_) -> a
        | A.Snd, PairVal (_,b) -> b
        | _ -> raise @@ InterpFatal __LOC__
      end
    | A.SizeExp exp ->
      let v = _E exp in
      IntVal (V.size v)
    | A.OpExp {left;oper;right} ->
      let v1 = _E left in
      let v2 = _E right in
      if ctxt.unsafe
      then op_unsafe oper v1 v2
      else op oper v1 v2
    | A.PairExp (a,b) ->
      PairVal (_E a,_E b)
    | A.ArrayExp {data=arr} ->
      let length = List.length arr in
      let data = arr |> List.map (fun e -> _E e) |> Array.of_list in
      ArrayVal {length;data}
    | A.NilExp -> 
      let addr = -1 in
      let cell_size = 0 in
      PointerVal{addr; cell_size}
    | A.ErrExp -> 
      (ErrVal{padding=[||]; elem_size=0})
    (* TODO:  *)
    | A.ReadExp {var; idx; default} ->
      let v = readvar ctxt var in
      let i = _int @@ _E idx in
      let d = _E default in
      match v with
    | ArrayVal {length; data} ->
      let maxidx = length - 1 in
      let result = ref d in
      for j = 0 to maxidx do
        let use = Bool.to_int (j = i) in
        let size_j = V.size data.(j) in
        let good_size = if size_j <= V.size d then 1 else 0 in
        let mode = good_size * use in
        (* Get back a value with the same size as default (public) *)
        let r = sizeSafeSelectWithDefault data.(j) d mode in
        (* Safe select with what you get back, both result and r are of the same size (result starts w/ default) so it's size oblivious *)
        result := safeSelect mode !result r;
        if mode = 1 then begin
          print_int j;
          print_string " |> A: ";
          print_string (V.to_string data.(i));
          print_string " - ";
          print_int (V.size data.(i));
          print_string "    \tD: ";
          print_string (V.to_string d);
          print_string " - ";
          print_int (V.size d);
          print_string "    \t-> ";
          print_string (V.to_string !result);
          print_string " - ";
          print_int (V.size !result);
          print_string "\n"
        end 
      done;
      !result
      | _ -> raise @@ InterpFatal "ReadExp: not an array"
  in _E

exception Exit

let interpCmd ctxt =
  let rec _I bitstack (A.Cmd{cmd_base;pos} as cmd) =
    let bit =
      match bitstack with
      | b::_ -> b
      | [] -> raise @@ InterpFatal "bitstack empty" in
    match cmd_base with
    | SkipCmd -> bitstack
    | SeqCmd {c1;c2} ->
      _I (_I bitstack c1) c2
    | AssignCmd { var; exp } ->
      begin 
      match bit with
      | 0 -> ()
      | _ ->
        let v = eval ctxt exp in
        writevar ctxt ASSIGN v 1 var
      end;
      bitstack
    | BindCmd { var; exp } when ctxt.unsafe ->
      begin 
        match bit with
        | 0 -> ()
        | _ ->
          let v = eval ctxt exp in
          writevar ctxt ASSIGN v 1 var
      end;
      bitstack
    | BindCmd { var; exp } ->
      let v = eval ctxt exp in
      writevar ctxt BIND v bit var;
      bitstack
    | InputCmd { var; _ } when ctxt.unsafe ->
      let arr = ctxt.input_buffer in
      let len = Array.length arr in
      let blank = Array.make len '\000' in
      let j = ref 0 in
      if (bit = 1) then (
        begin
        try 
          for i = 0 to len-1 do
            let c = arr.(i) in
            if c <> '\000'
            then Array.set blank i c
            else raise Unequal
          done;
        with Unequal -> ();
        end;
        writevar ctxt ASSIGN (StringVal{length=(!j);data=blank}) bit var;
      );
      bitstack
    | InputCmd { var; size; _ } ->
      let max_len = Array.length ctxt.input_buffer in
      let n = _int @@ eval ctxt size in
      let len = min n max_len in
      let data = Array.sub ctxt.input_buffer 0 len in
      let updbit = Bool.to_int @@ (data.(0) <> '\000') in
      let shouldBind = bit land updbit in
      let str = StringVal{length=Array.length data;data} in
      writevar ctxt BIND str shouldBind var;

      let blank = Array.make len '\000' in
      let buf_upd =
        Array.append
          (Array.sub ctxt.input_buffer len (max_len - len))
          blank in
      let s1 = StringVal{length=max_len;data=ctxt.input_buffer} in
      let s2 = StringVal{length=max_len;data=buf_upd} in
      begin
        match safeSelect shouldBind s1 s2 with
        | StringVal{data;_} ->
          ctxt.input_buffer <- data
        | _ -> raise @@ InterpFatal "InputCmd"
      end;
      bitstack
    | OutputCmd { ch; exp } ->
      let v = eval ctxt exp in
      if bit = 1 then print_endline @@ ch ^ "> " ^ V.to_string v;
      bitstack
    | SendCmd { channel; exp } when ctxt.unsafe ->
      if (bit = 1) then (
        let (bitlvl,ty) = lookup ctxt.trust_map channel in
        let lbit = M.Lbit{bit; level=bitlvl} in
        let tvalue = M.TypedVal{value=eval ctxt exp; ty} in
        let msg = M.Relay{sender=ctxt.name;channel;lbit;tvalue} in
        send ctxt msg
      );
      bitstack
    | SendCmd { channel; exp } ->
      let (bitlvl,ty) = lookup ctxt.trust_map channel in
      let lbit = M.Lbit{bit; level=bitlvl} in
      let tvalue = M.TypedVal{value=eval ctxt exp; ty} in
      let msg = M.Relay{sender=ctxt.name;channel;lbit;tvalue} in
      send ctxt msg;
      bitstack
    | IfCmd { test; thn; els } ->
      begin
      match eval ctxt test with
      | IntVal 0 -> _I bitstack els
      | _ -> _I bitstack thn
      end
    | WhileCmd { test; body } ->
      begin
      match eval ctxt test with
      | IntVal 0 -> bitstack
      | _ -> (_I (_I bitstack body) cmd)
      end
    | OblivIfCmd { test; thn; els } when ctxt.unsafe ->
      begin
      match eval ctxt test with
      | IntVal 0 -> _I bitstack els
      | _ -> _I bitstack thn
      end
    | OblivIfCmd { test; thn; els } ->
      let v = eval ctxt test in
      let i =
        match v with
        | IntVal n -> Bool.to_int @@ (n <> 0)
        | _ -> 1 in
      let (~>) cmd_base = A.Cmd{cmd_base;pos} in
      let (++) c1 c2 = ~> (A.SeqCmd{c1;c2}) in
      let bitstack = i land bit :: (i lxor 1) land bit :: bitstack in
      let c = thn ++ (~> A.PopCmd) ++ els ++ (~> A.PopCmd) in
      _I bitstack c
    | PopCmd ->
      begin
      match bitstack with
      | [] -> raise @@ InterpFatal ("PopCmd: stack empty")
      | _ :: bitstack' -> bitstack'
      end
    | AllocCmd {var; exp; cell_size} ->
      if bit = 1 then (
        let v = eval ctxt exp in
        let c = _int @@ eval ctxt cell_size in
        let addr = ctxt.next_address in
        H.add ctxt.heap addr v;
        ctxt.next_address <- ctxt.next_address + 1;
        writevar ctxt ASSIGN (PointerVal{ addr; cell_size=c}) 1 var
      );
      bitstack
    (* P: Test *)
    | OblivAllocCmd {var; exp; cell_size} ->
      let v = eval ctxt exp in
      let c = _int @@ eval ctxt cell_size in
      let addr = ctxt.next_address in
      H.add ctxt.heap addr v;
      ctxt.next_address <- ctxt.next_address + 1;
      writevar ctxt BIND (PointerVal{ addr; cell_size=c}) bit var;
      bitstack
    | ExitCmd ->
      send ctxt (M.Goodbye {sender=ctxt.name});
      raise Exit
      in
  _I

let rec interp_loop ctxt () =
  begin
  match dequeue ctxt.message_queue with
  | Some (M.Relay{lbit=M.Lbit{bit=0;_};_}) when ctxt.unsafe ->
    ()
  | Some (M.Relay{lbit=M.Lbit{bit=0;level};_}) when L.flows_to level L.bottom  ->
    ()
  | Some (M.Relay{sender;channel=C.Ch{handler;_};lbit=M.Lbit{bit;_};tvalue=M.TypedVal{value;_};_} as msg) ->
    if (not @@ String.equal sender ctxt.name)
    then Tr.add_receive (Sys.time()) msg ctxt.trace;
    begin
      match H.find_opt ctxt.handlers handler with
      | Some {x;body} ->
        H.add ctxt.memory x value;
        let _ = interpCmd ctxt [bit] body in
        H.clear ctxt.memory;
      | None -> ()
    end
  | Some (Goodbye {sender="OBLIVIO"}) -> exit 1;
  | _ -> ();
  end;
  T.yield ();
  interp_loop ctxt ()

let rec input_loop ctxt () =
  begin
  enqueue (input_value ctxt.server.input) ctxt.message_queue;
  end;
  T.yield ();
  input_loop ctxt ()

let rec prompt ctxt () =
  let line = read_line () in
  let arr = line |> String.to_seq |> Array.of_seq in
  let l1 = Array.length arr in
  let l2 = Array.length ctxt.input_buffer in
  Array.blit arr 0 ctxt.input_buffer 0 (min l1 l2);
  T.yield ();
  prompt ctxt ()


let interp ?(unsafe=false) print_when print_what (A.Prog{node;decls;hls}) =
  let inet_addr = Unix.inet_addr_of_string "127.0.0.1" in
  let sockaddr = Unix.ADDR_INET (inet_addr,3050) in
  let input,output = Unix.open_connection sockaddr in

  let ctxt =
    { name = node
    ; unsafe
    ; message_queue = 
      { lock = Mutex.create ()
      ; queue = Queue.create ()
      }
    ; input_buffer = Array.make 256 '\000'
    ; memory = H.create 1024
    ; store = H.create 1024
    ; heap = H.create 1024
    ; next_address = 0
    ; handlers = H.create 1024
    ; trust_map = H.create 1024
    ; server = {input;output}
    ; trace = Tr.empty_trace print_when print_what
    } in
  let f (A.Hl{handler;x;body;_}) =
    H.add ctxt.handlers handler {x;body} in
  let g = function
    | (A.VarDecl{x;init;_}) ->
      let i = eval ctxt init in
      H.add ctxt.store x i

    | (A.VarDeclHeap{x;init;cell_size;_}) ->
      let v = eval ctxt init in
      let c = _int @@ eval ctxt cell_size in
      let addr = ctxt.next_address in
      if (c < V.size v) then raise @@ InterpFatal "assigning oversized value into heap"
      else
      H.add ctxt.heap addr v;
      ctxt.next_address <- ctxt.next_address + 1;
      H.add ctxt.store x (PointerVal{addr; cell_size=c})
    | (A.LocalChannelDecl _) ->
      ()
    | (A.NetworkChannelDecl{channel;ty;level;_}) ->
      H.add ctxt.trust_map channel (level,ty) in
  
  List.iter f hls;
  List.iter g decls;

  send ctxt (M.Greet {sender=ctxt.name});

  let _ = T.create (prompt ctxt) () in

  let _ = T.create (input_loop ctxt) () in

  try
    interp_loop ctxt ()
  with Exit ->
    Tr.terminate ctxt.trace
  