module T = Thread
module H = Hashtbl
module M = Common.Message
module L = Common.Level
module A = Common.Tabsyn
module V = Common.Value
module Ty = Common.Types
module Tr = Common.Trace
module C = Common.Channel
module Heap = Common.Heap
module PH = Common.Perfecthash


open Common.Value
open Common.Oper

type handler_info = {x: string; body: A.cmd}
type server_info = {input: in_channel; output: out_channel}

type 'a sync_queue =
  { lock: Mutex.t
  ; queue: 'a Queue.t
  }

type timing =
  { index_s: float
  ; index_write_s: float
  ; deref_s: float
  ; map_s: float
  ; map_write_s: float
  ; heap_write_s: float
  ; index_sleep: float ref;       index_wc: float ref
  ; index_write_sleep: float ref; index_write_wc: float ref
  ; deref_sleep: float ref;       deref_wc: float ref
  ; map_sleep: float ref;         map_wc: float ref
  ; map_write_sleep: float ref;   map_write_wc: float ref
  ; heap_write_sleep: float ref;   heap_write_wc: float ref
  ; calib_s: float
  ; prog_start: float
  }

type context =
  { name: string
  ; unsafe: bool
  ; message_queue: M.message sync_queue
  ; mutable input_buffer: char array
  ; memory: (string, value) H.t
  ; store: (string, value) H.t
  ; heap: Heap.t
  ; handlers: (string, handler_info) H.t
  ; trust_map: (C.channel, L.level * Ty.ty) H.t
  ; server: server_info
  ; trace: Tr.trace
  ; timing: timing
  }

let dummy_pointer = 0

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
let rec dummy_of_size (ty: Ty.basetype) (size: int) : value =
  match ty with
  | Ty.INT ->
    IntVal{error=1; value=0}
  | Ty.PATH (_, s) ->
    PathVal{error=1; size=s; addr=0}
  | Ty.ARRAY inner_ty ->
    let word = Sys.word_size / 8 in
    let n = max 0 ((size - 3) / word) in
    let data = Array.init n (fun _ -> dummy_of_size (Ty.base inner_ty) word) in
    ArrayVal{error=1; length=0; data}
  | Ty.PAIR (a_ty, b_ty) ->
    let word = Sys.word_size / 8 in
    let a = dummy_of_size (Ty.base a_ty) word in
    let b = dummy_of_size (Ty.base b_ty) (size - 3 - word) in
    PairVal{error=1; data=(a, b)}
  | _ ->
    let data = Array.make (max 0 (size - 3)) '\x00' in
    StringVal{error=1; length=0; data}

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

let safeSelect (_timing: timing) (bit: int) (orig: value) (upd: value) =
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
      let error = ((bit lxor 1) * e1) lor (bit * e2) in
      let length = ((1 lxor bit)*l1) lor (bit*l2) in
      let arrlen1, arrlen2 = Array.length d1, Array.length d2 in
      let data = if arrlen1 < arrlen2 then Array.copy d2 else Array.copy d1 in
      for i = 0 to (min arrlen1 arrlen2) - 1 do
        data.(i) <- _S d1.(i) d2.(i)
      done;
      ArrayVal{error; length; data}
    | HMapVal{error=e1; a=a1; m=m1; data=d1}, HMapVal{error=e2; a=a2; m=m2; data=d2} ->
      let error = ((bit lxor 1) * e1) lor (bit * e2) in
      let a = ((bit lxor 1) * a1) lor (bit * a2) in
      let m = ((bit lxor 1) * m1) lor (bit * m2) in
      let arrlen1, arrlen2 = Array.length d1, Array.length d2 in
      let data = if arrlen1 < arrlen2 then Array.copy d2 else Array.copy d1 in
      for i = 0 to (min arrlen1 arrlen2) - 1 do
        data.(i) <- (match d1.(i), d2.(i) with
          | Some v1, Some v2 -> Some (_S v1 v2)
          | o1, o2 -> if bit = 0 then o1 else o2)
      done;
      HMapVal{error; a; m; data}
    | PathVal{error=e1; size=s1; addr=v1}, PathVal{error=e2; size=s2; addr=v2} ->
      let err = ((bit lxor 1) * e1) lor (bit * e2) in
      let size = ((bit lxor 1) * s1) lor (bit * s2) in
      let addr = ((bit lxor 1) * v1) lor (bit * v2) in
      PathVal{error=err; size; addr}
    | _ -> raise @@ InterpFatal ("safeSelect: " ^ (V.to_string orig) ^  ", " ^ (V.to_string upd)) in
  _S orig upd

let timed_path_write (timing: timing) heap error addr size (block_ty: Ty.basetype) upd =
  if V.size upd > size then
    raise @@ InterpFatal (Printf.sprintf "timed_path_write: value size %d exceeds path size %d" (V.size upd) size);
  let dummy = dummy_of_size block_ty size in
  let to_write = safeSelect timing 1 dummy upd in

  let wc = timing.heap_write_s in
  let start = Unix.gettimeofday () in
  if (error != 1 && addr != dummy_pointer) then Heap.write heap addr to_write;
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in
  Unix.sleepf sleep;
  timing.heap_write_sleep := !(timing.heap_write_sleep) +. sleep;
  timing.heap_write_wc := !(timing.heap_write_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_path_write: elapsed %f exceeded worst-case %f" elapsed wc)

let timed_path_read (timing: timing) heap error addr (block_ty: Ty.basetype) size =
  let wc = timing.deref_s in
  let safe_addr = ((error lxor 1) * addr) lor (error * dummy_pointer) in
  let dummy = dummy_of_size block_ty size in
  let start = Unix.gettimeofday () in
  let heap_result =
    match Heap.read heap safe_addr with
    | v -> v
    | exception Heap.HeapError _ -> dummy
  in
  let result = set_error heap_result error in
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in
  Unix.sleepf sleep;
  timing.deref_sleep := !(timing.deref_sleep) +. sleep;
  timing.deref_wc := !(timing.deref_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_path_read: elapsed %f exceeded worst-case %f" elapsed wc);
  result

let timed_array_read (timing: timing) (data: value array) (error: int) (length: int) (idx: int) (dummy: value) : value =
  let wc = timing.index_s in

  let in_bounds = Bool.to_int (idx >= 0) land Bool.to_int (idx < length) land Bool.to_int (error = 0) in

  let safe_idx = in_bounds * idx in
  let start = Unix.gettimeofday () in
  let result = if in_bounds = 1 then data.(safe_idx) else dummy in
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in

  Unix.sleepf sleep;
  timing.index_sleep := !(timing.index_sleep) +. sleep;
  timing.index_wc := !(timing.index_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_array_read: elapsed %f exceeded worst-case %f" elapsed wc);
  set_error result error

let timed_array_write (timing: timing) (data: value array) (error: int) (length: int) (idx: int) (upd: value) : unit =
  let wc = timing.index_write_s in
  let in_bounds = Bool.to_int (idx >= 0) land Bool.to_int (idx < length) land Bool.to_int (error = 0) in
  let safe_idx = in_bounds * idx in
  let start = Unix.gettimeofday () in
  if in_bounds = 1 then data.(safe_idx) <- upd;
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in
  Unix.sleepf sleep;
  timing.index_write_sleep := !(timing.index_write_sleep) +. sleep;
  timing.index_write_wc := !(timing.index_write_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_array_write: elapsed %f exceeded worst-case %f" elapsed wc)

let timed_map_read (timing: timing) (map: value) (key: value) (dummy: value) : value =
  let wc = timing.map_s in
  let start = Unix.gettimeofday () in
  let result = match PH.lookup map key with Some v -> v | None -> dummy in
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in
  Unix.sleepf sleep;
  timing.map_sleep := !(timing.map_sleep) +. sleep;
  timing.map_wc := !(timing.map_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_map_read: elapsed %f exceeded worst-case %f" elapsed wc);
  result

let timed_map_write (timing: timing) (map: value) (key: value) (upd: value) : unit =
  let wc = timing.map_write_s in
  let start = Unix.gettimeofday () in
  PH.update map key upd;
  let elapsed = Unix.gettimeofday () -. start in
  let sleep = max 0.0 (wc -. elapsed) in
  Unix.sleepf sleep;
  timing.map_write_sleep := !(timing.map_write_sleep) +. sleep;
  timing.map_write_wc := !(timing.map_write_wc) +. wc;
  if elapsed > wc then raise @@ InterpFatal (Printf.sprintf "timed_map_write: elapsed %f exceeded worst-case %f" elapsed wc)

let op (timing: timing) oper v1 v2 =
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
  | CoalesceOp, a, b ->
    safeSelect timing (V.get_error a) a b
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

type update = ASSIGN | BIND

let time_op (f: unit -> unit) : float =
  let start = Unix.gettimeofday () in
  f ();
  Unix.gettimeofday () -. start

let calibrate iterations multiplier: timing =
  let samples = Buffer.create (iterations * 5 * 20) in
  Buffer.add_string samples "op,time_s\n";

  let max_of iters label f =
    let m = ref 0.0 in
    for _ = 1 to iters do
      let t = time_op f in
      Buffer.add_string samples (label ^ "," ^ string_of_float t ^ "\n");
      if t > !m then m := t
    done;
    !m
  in

  let arr_size = 256 in
  let dummy_int = IntVal{error=0; value=0} in
  let data = Array.make arr_size dummy_int in

  let index_s =
    let r = max_of iterations "array_read" (fun () ->
      let idx = Random.int arr_size in
      let _ = if idx < arr_size then data.(idx) else dummy_int in
      ())
    in r *. multiplier
  in

  let index_write_s =
    let r = max_of iterations "array_write" (fun () ->
      let idx = Random.int arr_size in
      data.(idx) <- IntVal{error=0; value=idx})
    in r *. multiplier
  in

  let heap = Heap.create () in
  let addr = Heap.alloc heap dummy_int in

  let deref_s =
    let r = max_of iterations "heap_read" (fun () ->
      let _ = match Heap.read heap addr with v -> v | exception Heap.HeapError _ -> dummy_int in
      ())
    in r *. multiplier
  in

  let heap_write_s =
    let r = max_of iterations "heap_write" (fun () ->
      Heap.write heap addr (IntVal{error=0;value=42}))
    in r *. multiplier
  in

  let map_kvs =
    let pairs = Array.init arr_size (fun i ->
      PairVal{error=0; data=(IntVal{error=0;value=i}, IntVal{error=0;value=i})})
    in
    ArrayVal{error=0; length=arr_size; data=pairs}
  in
  let map = PH.build map_kvs (Some dummy_int) in

  let map_s =
    let r = max_of iterations "map_read" (fun () ->
      let k = IntVal{error=0; value=Random.int arr_size} in
      let _ = PH.lookup map k in
      ())
    in r *. multiplier
  in

  let map_write_s =
    let r = max_of iterations "map_write" (fun () ->
      let k = IntVal{error=0; value=Random.int arr_size} in
      PH.update map k dummy_int)
    in r *. multiplier
  in

  let oc = open_out "calibration.csv" in
  Buffer.output_buffer oc samples;
  close_out oc;
  { index_s; index_write_s; deref_s; map_s; map_write_s; heap_write_s
  ; index_sleep       = ref 0.0; index_wc       = ref 0.0
  ; index_write_sleep = ref 0.0; index_write_wc = ref 0.0
  ; deref_sleep       = ref 0.0; deref_wc       = ref 0.0
  ; map_sleep         = ref 0.0; map_wc         = ref 0.0
  ; map_write_sleep   = ref 0.0; map_write_wc   = ref 0.0
  ; heap_write_sleep   = ref 0.0; heap_write_wc   = ref 0.0
  ; calib_s = 0.0; prog_start = 0.0 }



let rec readvar ctxt =
  let rec _V access_path (A.Var{var_base;loc;ty;_}) = match var_base with
    | A.SimpleVar x ->
      let v = 
        match loc with
        | LOCAL -> lookup ctxt.memory x
        | STORE -> lookup ctxt.store x in
      let rec unwrap_indices access_elem v cur_ty =
        match access_elem, v with
        | [], _ -> v
        | (idx,idx_lvl,arr_lvl)::idx_tl, ArrayVal{length;data;error} ->
          let elem_ty = match Ty.base cur_ty with
            | Ty.ARRAY content -> content
            | _ -> raise @@ InterpFatal "readVar: expected array type"
          in
          let out_of_bounds = Bool.to_int (idx >= length) lor Bool.to_int (idx < 0) in
          if (L.flows_to idx_lvl L.bottom && L.flows_to arr_lvl L.bottom) || ctxt.unsafe
          then
            if (out_of_bounds = 1)
              then raise @@ InterpFatal "readVar: out of bounds public read"
              else unwrap_indices idx_tl data.(idx) elem_ty
          else begin
            let dummy = dummy_of_size (Ty.base elem_ty) 0 in
            let result = unwrap_indices idx_tl (timed_array_read ctxt.timing data error length idx dummy) elem_ty in
            set_error result (V.get_error result lor error)
          end
        | _ -> raise @@ InterpFatal "readVar - Unhandled unwrap case"
      in
      unwrap_indices access_path v ty
    | A.SubscriptVar {var;exp} ->
      let A.Exp{ty=index_ty;_} = exp in
      let A.Var{ty=arr_ty;_} = var in
      let i = _int @@ eval ctxt exp in
      let index_lvl = Ty.level index_ty in
      let arr_lvl = Ty.level arr_ty in
      _V ((i, index_lvl, arr_lvl)::access_path) var
    | A.MapVar {var;exp} ->
      let A.Exp{ty=key_ty;_} = exp in
      let key_lvl = Ty.level key_ty in
      let map_lvl = Ty.level (let A.Var{ty;_} = var in ty) in
      let map_val = _V [] var in
      let key = eval ctxt exp in
      begin match map_val with
      | HMapVal _ ->
        if (L.flows_to key_lvl L.bottom && L.flows_to map_lvl L.bottom) || ctxt.unsafe then
          (match PH.lookup map_val key with Some v -> v | None -> raise @@ InterpFatal "MapVar: bad lookup")
        else
          let dummy = dummy_of_size (Ty.base ty) 0 in
          timed_map_read ctxt.timing map_val key dummy
      | _ -> raise @@ InterpFatal "MapVar: not a map"
      end
    | A.HeapVar {var} ->
      let ptr = _V access_path var in
      begin match ptr with
      | PointerVal{error; addr} ->
        if (error = 1) then raise @@ InterpFatal "HeapVar: public pointer is error";
        Heap.read ctxt.heap addr
      | PathVal{error; addr; size} ->
        timed_path_read ctxt.timing ctxt.heap error addr (Ty.base ty) size
      | _ -> raise @@ InterpFatal "HeapVar: not a pointer or path"
      end
in _V []

and writevar ctxt updkind upd mode =
  let rec _V path (A.Var{var_base;ty;_}) = match var_base with
    | A.SimpleVar x ->
      let v = lookup ctxt.store x in
      let rec f path v mode cur_ty =
        match path, v with
        | [], _ ->
          begin
          match updkind, ctxt.unsafe with
          | BIND, false ->
            let orig = lookup ctxt.store x in
            H.add ctxt.store x @@ safeSelect ctxt.timing mode orig upd
          | _ -> if mode = 1 then
            H.add ctxt.store x upd
          end
        | [(idx,idx_lvl,arr_lvl)], ArrayVal{length;data; error} ->
          let elem_ty = match Ty.base cur_ty with
            | Ty.ARRAY content -> content
            | _ -> raise @@ InterpFatal "writeVar: expected array type"
          in
          if (L.flows_to idx_lvl L.bottom && L.flows_to arr_lvl L.bottom) || ctxt.unsafe then
            if idx > length - 1 || idx < 0 then
              raise @@ InterpFatal "WriteVar: indexing array out of bounds"
            else
              match updkind, ctxt.unsafe with
              | BIND, false -> raise @@ InterpFatal "WriteVar: Array public bind?"
              | _ -> if mode = 1 then data.(idx) <- upd;
          else begin
            match updkind, ctxt.unsafe with
            | BIND, false ->
              let dummy = dummy_of_size (Ty.base elem_ty) 0 in
              let old_val = timed_array_read ctxt.timing data error length idx dummy in
              timed_array_write ctxt.timing data error length idx (safeSelect ctxt.timing mode old_val upd)
            | _ -> if mode = 1 then timed_array_write ctxt.timing data error length idx upd
          end
        | (i,idx_lvl,arr_lvl)::tl, ArrayVal{length;data;error} ->
          let elem_ty = match Ty.base cur_ty with
            | Ty.ARRAY content -> content
            | _ -> raise @@ InterpFatal "writeVar: expected array type"
          in
          let maxidx = length - 1 in
          let cnd1 = Bool.to_int(i >= 0) in
          let cnd2 = Bool.to_int(i > maxidx) in
          let idx = cnd1 * i in
          let idx = ((cnd2 lxor 1) * idx) lor (cnd2 * maxidx) in
          if (L.flows_to idx_lvl L.bottom && L.flows_to arr_lvl L.bottom) || ctxt.unsafe
          then f tl data.(idx) mode elem_ty
          else
            begin match tl with
            | [] ->
              let dummy = dummy_of_size (Ty.base elem_ty) 0 in
              begin match updkind, ctxt.unsafe with
              | BIND, false ->
                let old_val = timed_array_read ctxt.timing data error length idx dummy in
                timed_array_write ctxt.timing data error length idx (safeSelect ctxt.timing mode old_val upd)
              | _ -> if mode = 1 then timed_array_write ctxt.timing data error length idx upd
              end
            | _ -> raise @@ InterpFatal "writeVar: nested private array (impossible by semant)"
            end
        | _ -> raise @@ InterpFatal "writeVar"
        in
      f path v mode ty

    | A.SubscriptVar {var;exp} ->
      let A.Exp{ty=index_ty;_} = exp in
      let idx = _int @@ eval ctxt exp in
      let index_lvl = Ty.level index_ty in
      let arr_lvl = Ty.level (let A.Var{ty;_} = var in ty) in
      _V ((idx, index_lvl, arr_lvl)::path) var

    | A.MapVar {var;exp} ->
      let A.Exp{ty=key_ty;_} = exp in
      let key_lvl = Ty.level key_ty in
      let map_lvl = Ty.level (let A.Var{ty;_} = var in ty) in
      let map_val = readvar ctxt var in
      let key = eval ctxt exp in
      begin match map_val with
      | HMapVal _ ->
        if (L.flows_to key_lvl L.bottom && L.flows_to map_lvl L.bottom) || ctxt.unsafe then begin
          match updkind, ctxt.unsafe with
          | BIND, false -> 
            let old_val = (match PH.lookup map_val key with Some v -> v | None -> raise @@ InterpFatal "MapVar: bad write") in
            PH.update map_val key (safeSelect ctxt.timing mode old_val upd);
          | _ -> if mode = 1 then PH.update map_val key upd;
          end else begin
          let dummy = dummy_of_size (Ty.base ty) 0 in
          match updkind, ctxt.unsafe with
          | BIND, false ->
            let old_val = match PH.lookup map_val key with Some v -> v | None -> dummy in
            timed_map_write ctxt.timing map_val key (safeSelect ctxt.timing mode old_val upd)
          | _ -> if mode = 1 then timed_map_write ctxt.timing map_val key upd
        end
      | _ -> raise @@ InterpFatal "MapVar: not a map"
      end

    | A.HeapVar {var} ->
      begin match readvar ctxt var with
      | PointerVal{error; addr} ->
        if (error = 1 || addr = 0) then raise @@ InterpFatal "writeVar: Heap - writing to err/nil";
        begin match updkind, ctxt.unsafe with
        | BIND, false ->
          let old_val = Heap.read ctxt.heap addr in
          Heap.write ctxt.heap addr (safeSelect ctxt.timing mode old_val upd)
        | _ -> if mode = 1 then Heap.write ctxt.heap addr upd
        end
      | PathVal{error; addr; size} ->
        begin match updkind, ctxt.unsafe with
        | BIND, false ->
          let old_val = timed_path_read ctxt.timing ctxt.heap error addr (Ty.base ty) size in
          timed_path_write ctxt.timing ctxt.heap error addr size (Ty.base ty) (safeSelect ctxt.timing mode old_val upd)
        | _ -> if mode = 1 then timed_path_write ctxt.timing ctxt.heap error addr size (Ty.base ty) upd
        end
      | _ -> raise @@ InterpFatal "HeapVar: not a pointer"
      end
in _V []

and eval ctxt =
  let rec _E (A.Exp{exp_base;ty=outer_ty;_}) =
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
        | A.Fst, PairVal{error; data=(a,_)} -> set_error a error
        | A.Snd, PairVal{error; data=(_,b)} -> set_error b error
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
      else op ctxt.timing oper v1 v2
    | A.PairExp (a,b) ->
      PairVal{error=0;data=(_E a,_E b)}
    | A.ArrayExp arr ->
      let length = List.length arr in
      let data = arr |> List.map (fun e -> _E e) |> Array.of_list in
      ArrayVal {error=0;length;data}
    | A.HMapExp arr ->
      let val_ty, lvl = match Ty.base outer_ty, Ty.level outer_ty with
        | Ty.HMAP (_, vt), l -> vt, l
        | _ -> raise @@ InterpFatal "HMapExp: expected hmap type"
      in
      let dummy =
        if L.flows_to lvl L.bottom then None
        else Some (dummy_of_size val_ty 0)
      in
      let v = _E arr in
      PH.build v dummy
    | A.NilExp -> 
      PointerVal{error=0;addr=dummy_pointer}
    | A.AllocExp e ->
      let v = _E e in
      let addr = Heap.alloc ctxt.heap v in
      PointerVal{error=0;addr}
    | A.OnilExp size ->
      PathVal{error=0; size; addr=dummy_pointer}
    | A.OramExp{value=e; size=ptr_size} ->
      let A.Exp{ty=inner_ty;_} = e in
      let v = _E e in
      let addr = Heap.reserve ctxt.heap in
      timed_path_write ctxt.timing ctxt.heap 0 addr ptr_size (Ty.base inner_ty) v;
      PathVal{error=0; size=ptr_size; addr}
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
        match safeSelect ctxt.timing shouldBind s1 s2 with
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
  let calib_start = Unix.gettimeofday () in
  let timing = calibrate 5000000 2.0 in
  (* let timing = { index_s = 0.00013; index_write_s = 0.00013; deref_s = 0.0006; map_s=0.00028; map_write_s=0.00028; heap_write_s=0.000204
  ; index_sleep       = ref 0.0; index_wc       = ref 0.0
  ; index_write_sleep = ref 0.0; index_write_wc = ref 0.0
  ; deref_sleep       = ref 0.0; deref_wc       = ref 0.0
  ; map_sleep         = ref 0.0; map_wc         = ref 0.0
  ; map_write_sleep   = ref 0.0; map_write_wc   = ref 0.0
  ; heap_write_sleep   = ref 0.0; heap_write_wc   = ref 0.0 *)
  (* ; calib_s = 0.0; prog_start = 0.0 } in *)

  let calib_s = Unix.gettimeofday () -. calib_start in
  let timing = {timing with calib_s} in

  let inet_addr = Unix.inet_addr_of_string "127.0.0.1" in
  let sockaddr = Unix.ADDR_INET (inet_addr,3050) in
  let input,output = Unix.open_connection sockaddr in

  let prog_start = calib_start in
  let timing = {timing with prog_start} in

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
    ; handlers = H.create 1024
    ; trust_map = H.create 1024
    ; server = {input;output}
    ; trace = Tr.empty_trace print_when print_what
    ; timing
    } in

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
    let t = ctxt.timing in
    let prog_s = Unix.gettimeofday () -. t.prog_start in
    let total_sleep = !(t.index_sleep) +. !(t.index_write_sleep) +. !(t.deref_sleep) +. !(t.map_sleep) +. !(t.map_write_sleep) +. !(t.heap_write_sleep) in
    let total_wc    = !(t.index_wc)    +. !(t.index_write_wc)   +. !(t.deref_wc)    +. !(t.map_wc)    +. !(t.map_write_wc)   +. !(t.heap_write_wc) in
    Printf.eprintf "calibration time: %fs\n" t.calib_s;
    Printf.eprintf "program runtime:  %fs\n" prog_s;
    Printf.eprintf "%-12s  %12s  %12s  %12s\n" "operation" "calib_s" "sleep_s" "wc_s";
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "index"       t.index_s       !(t.index_sleep)       !(t.index_wc);
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "index_write" t.index_write_s !(t.index_write_sleep) !(t.index_write_wc);
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "deref"       t.deref_s       !(t.deref_sleep)       !(t.deref_wc);
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "heap_write"  t.heap_write_s   !(t.heap_write_sleep) !(t.heap_write_wc);
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "map"         t.map_s         !(t.map_sleep)         !(t.map_wc);
    Printf.eprintf "%-12s  %12f  %12f  %12f\n" "map_write"   t.map_write_s   !(t.map_write_sleep)   !(t.map_write_wc);
    Printf.eprintf "%-12s  %12s  %12f  %12f\n" "total"      ""               total_sleep          total_wc;
    Tr.terminate ctxt.trace
  