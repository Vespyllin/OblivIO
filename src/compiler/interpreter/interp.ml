module T = Thread
module M = Common.Message
module L = Common.Level
module A = Common.Tabsyn
module V = Common.Value
module Ty = Common.Types
module Tr = Common.Trace
module C = Common.Channel
module Heap = Common.Heap
module ORAM = ORAM.Path_oram

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
  ; heap: Heap.t
  ; oram: (int, ORAM.state) H.t
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
  | IntVal {value;_} -> value
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
  | IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} -> 
    Bool.to_int(v1 lxor v2 = 0) land (e1 lxor 1) land (e2 lxor 1)
  | StringVal{error=e1;length=l1;data=d1}, StringVal{error=e2;length=l2;data=d2} ->
    let mismatch = ref (l1 lxor l2 lor e1 lor e2)  in
    let publen = min (Array.length d1) (Array.length d2) in
    let seclen = min l1 l2 in
    for i = 0 to publen-1 do
      let bit = Bool.to_int(i < seclen) in
      let i1 = Char.code @@ d1.(i) in
      let i2 = Char.code @@ d2.(i) in
      mismatch := (bit land (i1 lxor i2)) lor !mismatch
    done;
    Bool.to_int (!mismatch = 0)
  | PointerVal {error=e1; addr=a1}, PointerVal {error=e2; addr=a2} -> 
    Bool.to_int(a1 lxor a2 = 0) land (e1 lxor 1) land (e2 lxor 1)
  | PairVal{error=e1; data=(a1,a2)}, PairVal{error=e2; data=(b1,b2)} ->
    (safeEq a1 b1 * safeEq a2 b2) land (1 lxor (e1 lor e2))
  | ArrayVal{error=e1;length=l1;data=d1;_}, ArrayVal{error=e2;length=l2;data=d2;_} ->
    let mismatch = ref (l1 lxor l2 lor e1 lor e2)  in
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
  | IntVal {error=e1;value=a}, IntVal {error=e2;value=b} -> 
    Bool.to_int ((a = b) && (e1 + e2 = 0))
  | StringVal{error=e1;length=l1;data=d1}, StringVal{error=e2;length=l2;data=d2} ->
    begin
    try
      if l1 <> l2 then raise Unequal;
      if e1 + e2 > 0 then raise Unequal;
      for i = 0 to (min l1 l2)-1 do
        if d1.(i) <> d2.(i) then raise Unequal
      done;
      1
    with Unequal -> 0
    end
  | PairVal{data=(a1,a2);_}, PairVal {data=(b1,b2);_} ->
    (* TODO: fix? *)
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
    | IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
      let value = ((bit lxor 1) * v1) lor (bit * v2) in
      IntVal {error=err; value}
    | PointerVal {error=e1; addr=v1}, PointerVal {error=e2; addr=v2} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
      let addr = ((bit lxor 1) * v1) lor (bit * v2) in
      PointerVal {error=err; addr}
    | StringVal{error=e1; length=l1; data=d1}, StringVal{error=e2; length=l2; data=d2} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
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
        for i = arrlen1 to arrlen2-1 do
          data.(i) <- Char.chr @@ bit * (Char.code @@ d2.(i))
        done;
        StringVal{error=err; length; data}
      | _, arrlen2 ->
        let length = ((1 lxor bit)*l1) lor (bit*l2) in
        let data = Array.copy d1 in
        for i = 0 to arrlen2-1 do
          let i1 = (1 lxor bit) * (Char.code @@ d1.(i)) in
          let i2 = bit * (Char.code @@ d2.(i)) in
          data.(i) <- Char.chr @@ i1 lor i2
        done;
        for i = arrlen2 to Array.length d1-1 do
          data.(i) <- Char.chr @@ (1 lxor bit) * (Char.code @@ d1.(i))
        done;
        StringVal{error=err; length; data}
      end
    | PairVal{error=e1;data=(a1,a2)}, PairVal{error=e2;data=(b1,b2)} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
      PairVal{error=err;data=(_S a1 b1, _S a2 b2)}
    | ArrayVal{error=e1; length=l1; data=d1}, ArrayVal{error=e2; length=l2; data=d2} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
      begin
      match Array.length d1, Array.length d2 with
      | arrlen1, arrlen2 when arrlen1 < arrlen2 ->
        let length = ((1 lxor bit)*l1) lor (bit*l2) in
        let data = Array.copy d2 in
        for i = 0 to arrlen1-1 do
          data.(i) <- _S d1.(i) d2.(i)
        done;
        (* TODO: Set dummy err vals to 0? *)
        (* for i = 0 to arrlen2-1 do *)
          (* data.(i) <- _S d1.(i) d2.(i) *)
        (* done; *)
        ArrayVal{error=err; length; data}
      | _, arrlen2 ->
        let length = ((1 lxor bit)*l1) lor (bit*l2) in
        let data = Array.copy d1 in
        for i = 0 to arrlen2-1 do
          data.(i) <- _S d1.(i) d2.(i)
        done;
        ArrayVal{error=err; length; data}
      end
    | _ -> raise @@ InterpFatal ("safeSelect: " ^ (V.to_string orig) ^  ", " ^ (V.to_string upd)) in
  _S orig upd

let get_error = function
  | IntVal {error; _} -> error
  | StringVal {error; _} -> error
  | PointerVal {error; _} -> error
  | ArrayVal {error; _} -> error
  | _ -> 0

(* TODO: ERROR HANDLING *)
let op oper v1 v2 =
  match oper,v1,v2 with
  (* POLY *)
  | EqOp, _, _ ->
    IntVal {error=0; value=(safeEq v1 v2)}
  | NeqOp, _, _ ->
    IntVal {error=0; value=((safeEq v1 v2) lxor 1)}
  (* INT *)
  | LtOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 - v2 < 0)}
  | LeOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 - v2 <= 0)}
  | GtOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 - v2 > 0)}
  | GeOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 - v2 >= 0)}
  | AndOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 land v2 > 0)}
  | OrOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    let not_err = 1 lxor (e1 lor e2) in
    IntVal {error=0; value=not_err land Bool.to_int(v1 lor v2 > 0)}
  | PlusOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1+v2}
  | MinusOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1-v2}
  | TimesOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1*v2}
  (* STRING *)
  | CaretOp, StringVal {error=e1;length=l1;data=d1}, StringVal {error=e2;length=l2;data=d2} ->
    StringVal {error=e1 lor e2;length=l1+l2; data=safeConcat l1 d1 d2}
  (* ARRAY *)
  (* | CaretOp, ArrayVal {length=l1;data=d1}, ArrayVal {length=l2;data=d2} -> *)
    (* ArrayVal {length=l1+l2; data=(safeConcatArr l1 d1 d2)} *)
  | CoalesceOp, a, b ->
    safeSelect (get_error a) a b
  | _ -> raise @@ NotImplemented (V.to_string v1 ^ to_string oper ^ V.to_string v2)

let op_unsafe oper v1 v2 =
  match oper,v1,v2 with
  (* POLY *)
  | EqOp, _, _ ->
    IntVal {error=0; value=unsafeEq v1 v2}
  | NeqOp, _, _ ->
    IntVal {error=0; value=(unsafeEq v1 v2) lxor 1}
  (* INT *)
  | LtOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 < v2)}
  | LeOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 <= v2)}
  | GtOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 > v2)}
  | GeOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 >= v2)}
  | AndOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 <> 0 && v2 <> 0)}
  | OrOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=Bool.to_int(v1 <> 0 || v2 <> 0)}
  | PlusOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1+v2}
  | MinusOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1-v2}
  | TimesOp, IntVal {error=e1; value=v1}, IntVal {error=e2; value=v2} ->
    IntVal {error=e1 lor e2; value=v1*v2}
  (* STRING *)
  | CaretOp, StringVal {error=e1; length=l1; data=d1}, StringVal {error=e2; length=l2; data=d2} ->
    let d1' = Array.sub d1 0 l1 in
    let d2' = Array.sub d2 0 l2 in
    StringVal {error=e1 lor e2; length=l1+l2; data=Array.append d1' d2'}
  | CoalesceOp, a, _ -> a
  | _ -> raise @@ NotImplemented (V.to_string v1 ^ to_string oper ^ V.to_string v2)

let rec to_bytes (v: value) : bytes =
  let fixed_size = 11 in
  match v with
  | IntVal {error; value} ->
    (* print_string "to_bytes: writing int\n"; *)
    let b = Bytes.make fixed_size '\x00' in
    (* type tag: 1 = int *)
    Bytes.set_uint8 b 0 1;
    Bytes.set_uint8 b 1 error;
    Bytes.set_int64_be b 3 (Int64.of_int value);
    b
  | PathVal {error; size; addr} ->
    (* print_string "to_bytes: writing path\n"; *)
    let b = Bytes.make fixed_size '\x00' in
    (* type tag: 3 = path *)
    Bytes.set_uint8 b 0 3;
    Bytes.set_uint8 b 1 error;
    Bytes.set_uint8 b 2 size;
    Bytes.set_int64_be b 3 (Int64.of_int addr);
    b
  | StringVal {error; length; data} ->
    (* print_string "to_bytes: writing str\n"; *)
    let b = Bytes.make (3 + Array.length data) '\x00' in
    (* type tag: 4 = string *)
    Bytes.set_uint8 b 0 4;
    Bytes.set_uint8 b 1 error;
    Bytes.set_uint8 b 2 length;
    Array.iteri (fun i c -> Bytes.set b (3 + i) c) data;
    b
  | ArrayVal {error; length; data} ->
    (* encode each element and concatenate *)
    let elems = Array.map to_bytes data in
    let total = 3 + (Array.length data * fixed_size) in
    let b = Bytes.make total '\x00' in
    (* type tag: 5 = array *)
    Bytes.set_uint8 b 0 5;
    Bytes.set_uint8 b 1 error;
    Bytes.set_uint8 b 2 length;
    Array.iteri (fun i elem -> Bytes.blit elem 0 b (3 + i * fixed_size) fixed_size) elems;
    b
  | PairVal {error; data=(v1, v2)} ->
    let v1d = to_bytes v1 in
    let v2d = to_bytes v2 in
    let total = 3 + (2 * fixed_size) in
    let b = Bytes.make total '\x00' in
    Bytes.set_uint8 b 0 6;
    Bytes.set_uint8 b 1 error;
    Bytes.blit v1d 0 b 3 (Bytes.length v1d);
    Bytes.blit v2d 0 b (3 + (Bytes.length v1d)) (Bytes.length v2d);
    b
  | _ -> raise @@ InterpFatal "to_bytes: unsupported value type"

let rec from_bytes (target_type: Ty.basetype) (b: bytes) : value =
  let tag = Bytes.get_uint8 b 0 in
  let error = Bytes.get_uint8 b 1 in
  match target_type with
  | Ty.INT ->
    let value = Int64.to_int (Bytes.get_int64_be b 3) in
    let error = error lor (Bool.to_int (tag <> 1)) in
    IntVal {error; value}
  | Ty.PATH (_, s) ->
    (* let acq_size = Bytes.get_uint8 b 2 in *)
    (* if (acq_size != size) then raise @@ InterpFatal ("pointer sizes got mixed up. reading ptr of block size " ^ string_of_int acq_size ^ " when trying to deref ptr of block size" ^ string_of_int s); *)
    let size = s in
    let addr = Int64.to_int (Bytes.get_int64_be b 3) in
    let error = error lor (Bool.to_int (tag <> 3)) in
    PathVal {error; size; addr}
  | Ty.STRING ->
    let length = Bytes.get_uint8 b 2 in
    let data_len = Bytes.length b - 3 in
    let data = Array.init data_len (fun i -> Bytes.get b (3 + i)) in
    let error = error lor (Bool.to_int (tag <> 4)) in
    StringVal {error; length; data}
  | Ty.ARRAY inner_ty ->
    let length = Bytes.get_uint8 b 2 in
    let num_elems = length in
    let data = Array.init num_elems (fun i -> from_bytes (Ty.base inner_ty) (Bytes.sub b (3 + i * 11) 11)) in
    let error = error lor (Bool.to_int (tag <> 5)) in
    ArrayVal {error; length; data}
  | Ty.PAIR (v1, v2) ->
    let error = error lor (Bool.to_int (tag <> 6)) in
    let v1d =  from_bytes (Ty.base v1) (Bytes.sub b 3 11) in
    let v2d =  from_bytes (Ty.base v2) (Bytes.sub b (3 + 11) 11) in
    PairVal {error; data=(v1d,v2d)}
  | Ty.SELF t -> 
    begin match !t with
    | Some x -> from_bytes (Ty.base x) b
    | None -> raise @@ InterpFatal "uninitialized recursive type";
    end
  | _ -> raise @@ InterpFatal ("from_bytes: unsupported target type " ^ (Ty.base_to_string target_type))

let get_byte_size (v: value) : int =
  let fixed_size = 11 in
  match v with
  | IntVal _ -> fixed_size
  | PointerVal _ -> fixed_size
  | PathVal _ -> fixed_size
  | PairVal _ -> 3 + 2 * fixed_size
  | StringVal {data; _} -> 3 + Array.length data
  | ArrayVal {data; _} -> 3 + Array.length data * fixed_size

let rec set_err (v: value) error : value =
  match v with
  | IntVal {value; _} -> IntVal {error; value}
  | PointerVal {addr; _} -> PointerVal {error; addr}
  | PathVal {size;addr; _} -> PathVal {error; size; addr}
  | StringVal {length; data; _} -> StringVal {error; length; data}
  | ArrayVal {length; data; _} -> ArrayVal {error; length; data}
  | PairVal{data;_} -> PairVal{error; data}

let rec get_error = function
  | IntVal {error; _} -> error
  | PointerVal {error; _} -> error
  | PathVal {error; _} -> error
  | StringVal {error; _} -> error
  | ArrayVal {error; _} -> error
  | PairVal{error;_} -> error

let rec deep_copy = function
  | IntVal {error; value} -> IntVal {error; value}
  | PointerVal {error; addr} -> PointerVal {error; addr}
  | PathVal {error; size; addr} -> PathVal {error; size; addr}
  | StringVal {error; length; data} -> StringVal {error; length; data = Array.copy data}
  | ArrayVal {error; length; data} -> ArrayVal {error; length; data = Array.map deep_copy data}
  | PairVal{error;data=(a, b)} -> PairVal{error;data=(deep_copy a, deep_copy b)}

type update = ASSIGN | BIND

let rec readvar ctxt =
  let rec _V access_path (A.Var{var_base;loc;ty;_}) = match var_base with
    | A.SimpleVar x ->
      let v = 
        match loc with
        | LOCAL -> lookup ctxt.memory x
        | STORE -> lookup ctxt.store x in
      let rec unwrap_indices access_elem v =
        match access_elem, v with
        | [], _ -> deep_copy v
        | (idx,idx_lvl,arr_lvl)::idx_tl, ArrayVal{length;data;error} ->
          if (L.flows_to idx_lvl L.bottom && L.flows_to arr_lvl L.bottom) || ctxt.unsafe
            then if idx > length - 1 || idx < 0 then
              raise @@ InterpFatal "ReadVar: indexing array out of bounds"
            else
              unwrap_indices idx_tl data.(idx)
          else 
            let len = Array.length data in
            (* We can crash if length = 0, because size is public *)
            if (len = 0) then raise @@ InterpFatal "ReadVar: indexing array of size/length 0";

            let safe_value = ref (unwrap_indices idx_tl data.(0)) in
            let elem_err = ref 0 in
            for i = 0 to len-1 do
              let right_idx = (Bool.to_int (i lxor idx = 0)) in
              let rec_res = unwrap_indices idx_tl data.(i) in
              safe_value := safeSelect right_idx !safe_value rec_res;
              elem_err := (right_idx * get_error rec_res) lor (lnot right_idx * !elem_err)
            done;

            let new_err = Bool.to_int(idx >= length lor error lor !elem_err) in
            set_err (!safe_value) new_err

        | _ -> raise @@ InterpFatal "readVar"
        in
      unwrap_indices access_path v
    | A.SubscriptVar {var;exp} ->
      let A.Exp{ty=index_ty;_} = exp in
      let i = _int @@ eval ctxt exp in
      let index_lvl = Ty.level index_ty in
      let arr_lvl = Ty.level ty in
      _V ((i, index_lvl, arr_lvl)::access_path) var
    | A.HeapVar {var} ->
      let ptr = _V access_path var in
      let error, addr, size, oram = match ptr with
        | PointerVal{error; addr} -> error, addr, 0, false
        | PathVal{error; size; addr} -> error, addr, size, true
        | _ -> raise @@ InterpFatal "HeapVar: not a pointer 1" in
      
      if not oram then begin
        (* public pointer: direct heap access *)
        if (error = 1 || addr = 0) then raise @@ InterpFatal "readVar: Heap - reading from err/nil";
        Heap.read ctxt.heap addr
      end else begin
        (* Private pointer, obliviate *)
        if (H.find_opt ctxt.oram size = None) then H.add ctxt.oram size (ORAM.create ~capacity:16 ~block_size:((size*8) + 3) ~z:4);
        let correct_addr = (((error lxor 1) * addr) lor (error * 0)) in
        let base = Ty.base ty in
        from_bytes base (ORAM.read (H.find ctxt.oram size) correct_addr)
      end
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
        | [(idx,lvl)], ArrayVal{length;data; _} ->
          (* TODO: careful in case of array overwrite *)
          (* TODO: check also array level (public index+array) *)
          if L.flows_to lvl L.bottom || ctxt.unsafe then (* public index *)
            if idx > length - 1 || idx < 0 then
              raise @@ InterpFatal "ReadVar: indexing array out of bounds"
            else
              match updkind, ctxt.unsafe with
              | BIND, false ->
                data.(idx) <- safeSelect mode data.(idx) upd
              | _ ->
                if mode = 1 then data.(idx) <- upd;
            else (* non-public index *)
              let len = Array.length data in
              if (len = 0) then raise @@ InterpFatal "ReadVar: indexing array of size/length 0";

              for i = 0 to len-1 do
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
      let idx = _int @@ eval ctxt exp in
      let lvl = Ty.level ty in
      _V ((idx,lvl)::path) var
    | A.HeapVar {var} ->
      let error, addr, size, oram = match readvar ctxt var with
        | PointerVal{error; addr} -> error, addr, 0, false
        | PathVal{error; size;  addr} -> error, addr, size, true
        | _ -> raise @@ InterpFatal "HeapVar: not a pointer" in

      if not oram then begin
        if (error = 1 || addr = 0) then raise @@ InterpFatal "writeVar: Heap - writing to err/nil";
        match updkind, ctxt.unsafe with
        | BIND, false ->
          let old_val = Heap.read ctxt.heap addr in
          Heap.write ctxt.heap addr (safeSelect mode old_val upd)
        | _ ->
          if mode = 1 then Heap.write ctxt.heap addr upd
      end else begin
        let correct_addr = (((error lxor 1) * addr) lor (error * 0)) in
        (* TODO *)
        if (get_byte_size upd > (size * 8) + 3) then
          raise @@ InterpFatal ("HeapWrite: Value too large. Attempted to write element of size " ^ string_of_int(get_byte_size upd) ^ " into block of size " ^ string_of_int(0));

        if (H.find_opt ctxt.oram size = None) then H.add ctxt.oram size (ORAM.create ~capacity:16 ~block_size:((size*8) + 3) ~z:4);

        match updkind, ctxt.unsafe with
        | BIND, false ->
          let A.Var{ty;_} = var in
          let inner_ty = match Ty.base ty with
            | Ty.PATH (t, _) -> Ty.base t
            | Ty.POINTER t -> Ty.base t
            | _ -> raise @@ InterpFatal "HeapWrite: not a pointer type" in
          
          let old_val = from_bytes inner_ty (ORAM.read (H.find ctxt.oram size) correct_addr) in
          ORAM.write (H.find ctxt.oram size) correct_addr (to_bytes (safeSelect mode old_val upd))
        | _ ->
          if mode = 1 then ORAM.write (H.find ctxt.oram 0) correct_addr (to_bytes upd)
      end
in _V []

and eval ctxt =
  let rec _E (A.Exp{exp_base;_}) =
    match exp_base with
    | A.IntExp i -> IntVal{error=0;value=i}
    | A.StringExp s -> 
      let length = String.length s in
      let data = s |> String.to_seq |> Array.of_seq in
      StringVal {error=0;length;data}
    | A.VarExp v -> 
      readvar ctxt v
    | A.ProjExp {proj;exp} ->
      let v = _E exp in
      begin
        match proj,v with
        | A.Fst, PairVal{error; data=(a,_)} -> set_err a error
        | A.Snd, PairVal{error; data=(_,b)} -> set_err b error
        | _ -> raise @@ InterpFatal __LOC__
      end
    | A.SizeExp exp ->
      let v = _E exp in
      IntVal {error=0; value=V.size v}
    | A.OpExp {left;oper;right} ->
      let v1 = _E left in
      let v2 = _E right in
      if ctxt.unsafe
      then op_unsafe oper v1 v2
      else op oper v1 v2
    | A.PairExp (a,b) ->
      PairVal{error=0;data=(_E a,_E b)}
    | A.ArrayExp arr ->
      let length = List.length arr in
      let data = arr |> List.map (fun e -> _E e) |> Array.of_list in
      ArrayVal {error=0;length;data}
    | A.NilExp -> 
      PointerVal{error=0;addr=0}
      | A.AllocExp e ->
        let v = _E e in
        let addr = Heap.alloc ctxt.heap v in
        PointerVal{error=0;addr}
    | A.OnilExp size -> 
      PathVal{error=0; size; addr=0}
    | A.OramExp{value=e; size} ->
      if (size <= 0) then raise @@ InterpFatal ("ORAM: Size cannot be equal to or below 0. Size provided: " ^ string_of_int size);

      let v = _E e in
      let ptr_size = size*8 + 3 in

      if (get_byte_size v > ptr_size) then 
        raise @@ InterpFatal ("HeapWrite: Value too large. Attempted to write element of size " ^ string_of_int(get_byte_size v) ^ " into block of size " ^ string_of_int(ptr_size));

      if (H.find_opt ctxt.oram size = None) then H.add ctxt.oram size (ORAM.create ~capacity:16 ~block_size:ptr_size ~z:4);
      let addr = ORAM.alloc (H.find ctxt.oram size) (to_bytes v) in 
      PathVal{error=0; size; addr}
      
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
        writevar ctxt ASSIGN (StringVal{error=0;length=(!j);data=blank}) bit var;
      );
      bitstack
    | InputCmd { var; size; _ } ->
      let max_len = Array.length ctxt.input_buffer in
      let n = _int @@ eval ctxt size in
      let len = min n max_len in
      let data = Array.sub ctxt.input_buffer 0 len in
      let updbit = Bool.to_int @@ (data.(0) <> '\000') in
      let shouldBind = bit land updbit in
      let str = StringVal{error=0;length=Array.length data;data} in
      writevar ctxt BIND str shouldBind var;

      let blank = Array.make len '\000' in
      let buf_upd =
        Array.append
          (Array.sub ctxt.input_buffer len (max_len - len))
          blank in
      let s1 = StringVal{error=0;length=max_len;data=ctxt.input_buffer} in
      let s2 = StringVal{error=0;length=max_len;data=buf_upd} in
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
      | IntVal {value=0; _} -> _I bitstack els
      | _ -> _I bitstack thn
      end
    | WhileCmd { test; body } ->
      begin
      match eval ctxt test with
      | IntVal {value=0; _} -> bitstack
      | _ -> (_I (_I bitstack body) cmd)
      end
    | OblivIfCmd { test; thn; els } when ctxt.unsafe ->
      begin
      match eval ctxt test with
      | IntVal {value=0; _} -> _I bitstack els
      | _ -> _I bitstack thn
      end
    | OblivIfCmd { test; thn; els } ->
      let v = eval ctxt test in
      let i =
        match v with
        | IntVal {value; _} -> Bool.to_int @@ (value <> 0)
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
    ; heap = Heap.create ()
    ; oram = H.create 1024
    ; handlers = H.create 1024
    ; trust_map = H.create 1024
    ; server = {input;output}
    ; trace = Tr.empty_trace print_when print_what
    } in

  (* ORAM.create ~capacity:16 ~block_size:32 ~z:4 *)
  (* H.add ctxt.oram 0 (ORAM.create ~capacity:16 ~block_size:0 ~z:4); *)

  let f (A.Hl{handler;x;body;_}) =
    H.add ctxt.handlers handler {x;body} in
  let g = function
    | (A.VarDecl{x;init;_}) ->
      let i = eval ctxt init in
      H.add ctxt.store x i
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
  