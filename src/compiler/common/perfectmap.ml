(* Perfect Hashing over Path ORAM
   Keys are known at build time (runtime).
   Uses two-level perfect hashing with fixed-size padded buckets
   so bucket sizes are never observable. *)

open Value

module ORAM = Path_oram
module Ty   = Types
module L    = Level

exception PerfectHashFatal of string
exception InterpFatal of string

let rec to_bytes (v: value) : bytes =
  let fixed_size = 11 in
  match v with
  | IntVal {error; value} ->
    let b = Bytes.make fixed_size '\x00' in
    Bytes.set_uint8 b 0 1;
    Bytes.set_uint8 b 1 error;
    Bytes.set_int64_be b 3 (Int64.of_int value);
    b
  | PathVal {error; size; addr} ->
    let b = Bytes.make fixed_size '\x00' in
    Bytes.set_uint8 b 0 3;
    Bytes.set_uint8 b 1 error;
    Bytes.set_uint8 b 2 size;
    Bytes.set_int64_be b 3 (Int64.of_int addr);
    b
  | StringVal {error; length; data} ->
    let b = Bytes.make (3 + Array.length data) '\x00' in
    Bytes.set_uint8 b 0 4;
    Bytes.set_uint8 b 1 error;
    Bytes.set_uint8 b 2 length;
    Array.iteri (fun i c -> Bytes.set b (3 + i) c) data;
    b
  | ArrayVal {error; length; data} ->
    let elems = Array.map to_bytes data in
    let total = 3 + (Array.length data * fixed_size) in
    let b = Bytes.make total '\x00' in
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
    let addr = Int64.to_int (Bytes.get_int64_be b 3) in
    let error = error lor (Bool.to_int (tag <> 3)) in
    PathVal {error; size=s; addr}
  | Ty.STRING ->
    let length = Bytes.get_uint8 b 2 in
    let data_len = Bytes.length b - 3 in
    let data = Array.init data_len (fun i -> Bytes.get b (3 + i)) in
    let error = error lor (Bool.to_int (tag <> 4)) in
    StringVal {error; length; data}
  | Ty.ARRAY inner_ty ->
    let length = Bytes.get_uint8 b 2 in
    let data = Array.init length (fun i -> from_bytes (Ty.base inner_ty) (Bytes.sub b (3 + i * 11) 11)) in
    let error = error lor (Bool.to_int (tag <> 5)) in
    ArrayVal {error; length; data}
  | Ty.PAIR (v1, v2) ->
    let error = error lor (Bool.to_int (tag <> 6)) in
    let v1d = from_bytes (Ty.base v1) (Bytes.sub b 3 11) in
    let v2d = from_bytes (Ty.base v2) (Bytes.sub b (3 + 11) 11) in
    PairVal {error; data=(v1d,v2d)}
  | Ty.SELF t ->
    begin match !t with
    | Some x -> from_bytes (Ty.base x) b
    | None -> raise @@ InterpFatal "uninitialized recursive type"
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
  | _ -> raise @@ InterpFatal "not impl"

(* ------------------------------------------------------------------ *)
(* Parameters                                                           *)
(* ------------------------------------------------------------------ *)

let large_prime = 1000003
let max_tries   = 64

(* ------------------------------------------------------------------ *)
(* Hash functions                                                        *)
(* ------------------------------------------------------------------ *)

let make_hash () =
  { a = 1 + Random.int (large_prime - 1)
  ; b = Random.int large_prime
  }

let apply_hash h m key =
  abs ((h.a * key + h.b) mod large_prime) mod m

(* ------------------------------------------------------------------ *)
(* Slot encoding                                                         *)
(* ------------------------------------------------------------------ *)

let int_ty = Ty.Type{base=Ty.INT; errable=false; level=L.bottom}
let pair_ty vt = Ty.PAIR (int_ty, Ty.Type{base=vt; errable=false; level=L.bottom})

let encode_slot ~block_size key value : bytes =
  let pair = PairVal{error=0; data=(IntVal{error=0; value=key}, value)} in
  let vb   = to_bytes pair in
  let b    = Bytes.make block_size '\x00' in
  Bytes.blit vb 0 b 0 (min (Bytes.length vb) block_size);
  b

let decode_slot vt (b: bytes) : (int * value) option =
  if Bytes.get_uint8 b 0 = 0 then None
  else
    match from_bytes (pair_ty vt) b with
    | PairVal{data=(IntVal{value=key;_}, v); _} -> Some (key, v)
    | _ -> None

let dummy_block block_size = Bytes.make block_size '\x00'


let safeSelect bit a b = if bit = 1 then b else a

let oblivious_array_access arr key n =
  let result = ref arr.(0) in
  for i = 0 to n - 1 do
    let is_target = Bool.to_int (i = key) in
    result := safeSelect is_target !result arr.(i)
  done;
  !result



(* ------------------------------------------------------------------ *)
(* Build                                                                *)
(* ------------------------------------------------------------------ *)

(** Find a collision-free level-2 hash for [keys] in [m] slots.
    Always runs exactly [max_tries] iterations to hide timing.
    Sentinel value -1 is ignored (padding for oblivious key collection). *)
  (* TODO: Obliviate *)
let find_h2 keys m =
  let best   = ref (make_hash ()) in
  let solved = ref false in
  for _ = 1 to max_tries do
    let h    = make_hash () in
    let seen = Array.make m false in
    let ok   = ref true in
    for j = 0 to List.length keys - 1 do
      let k = List.nth keys j in
      if k <> -1 then begin
        let slot = apply_hash h m k in
        if seen.(slot) then ok := false
        else seen.(slot) <- true
      end
    done;
    if !ok && not !solved then begin
      best   := h;
      solved := true
    end
  done;
  if not !solved then
    raise @@ PerfectHashFatal "could not find collision-free h2 — increase max_tries or bucket_size";
  !best

(* find_tag function and store the tag + copy into the dummy block *)
let build (kvs: value) =
  let _err, _len, kvs_arr = match kvs with
  | ArrayVal {error; length; data} -> error, length, data
  | _ -> raise @@ PerfectHashFatal "not provided an array of k,v pairs" in

  let n         = Array.length kvs_arr in
  let n_buckets = max 1 n in
  let h1        = make_hash () in

  let bucket_size = 
    let log2n = max 1 (int_of_float (log (float_of_int n) /. log 2.0)) in
    max 4 (log2n * log2n) in

  (* TODO: Separate key and value *)
  let block_size = Array.fold_left (fun acc v -> max acc (get_byte_size v)) 0 kvs_arr in

  let capacity =
    let total = n_buckets * bucket_size in
    let p = ref 4 in
    while !p < total do p := !p * 2 done;
    !p
  in

  (* ---- Level 2: find collision-free h2 per bucket ---- *)
  (* Use 'length' to determine if its a valid key *)
  (* Use another array/pair instead of using '-1' *)
  let h2s = Array.make n_buckets (make_hash ()) in
  for i = 0 to n_buckets - 1 do
    let keys = Array.make n (-1) in
    for j = 0 to n - 1 do
      let k = match kvs_arr.(j) with
        | PairVal{data=(IntVal{value;_}, _);_} -> value
        | _ -> raise @@ PerfectHashFatal "map elements must be pairs with int keys" in
      let belongs = Bool.to_int (apply_hash h1 n_buckets k = i) in
      keys.(j) <- (belongs * k) + ((1 lxor belongs) * (-1))
    done;
    h2s.(i) <- find_h2 (Array.to_list keys) bucket_size
  done;

  (* ---- Create ORAM and fill with dummies ---- *)
  let oram = ORAM.create ~capacity ~block_size ~z:4 in
  for addr = 0 to n_buckets * bucket_size - 1 do
    ORAM.write oram addr (dummy_block block_size)
  done;

  (* ---- Write each KV pair to its ORAM address ----
     Obliviously select h2 by scanning all buckets. *)
  for j = 0 to n - 1 do
    let k, pair = match kvs_arr.(j) with
      | PairVal{data=(IntVal{value=k;_}, _);_} as p -> k, p
      | _ -> raise @@ PerfectHashFatal "map elements must be pairs with int keys" in
    let target_i = apply_hash h1 n_buckets k in
    let h2       = oblivious_array_access h2s target_i n_buckets in
    let slot     = apply_hash h2 bucket_size k in
    let addr     = target_i * bucket_size + slot in
    let b        = Bytes.make block_size '\x00' in
    let vb       = to_bytes pair in
    Bytes.blit vb 0 b 0 (min (Bytes.length vb) block_size);
    ORAM.write oram addr b
  done;

  { oram; h1; h2s; n_buckets; bucket_size; block_size }

(* ------------------------------------------------------------------ *)
(* Lookup — always exactly 2 ORAM accesses                            *)
(* ------------------------------------------------------------------ *)

let set_err (v: value) error : value =
  match v with
  | IntVal {value; _} -> IntVal {error; value}
  | PointerVal {addr; _} -> PointerVal {error; addr}
  | PathVal {size;addr; _} -> PathVal {error; size; addr}
  | StringVal {length; data; _} -> StringVal {error; length; data}
  | ArrayVal {length; data; _} -> ArrayVal {error; length; data}
  | PairVal{data;_} -> PairVal{error; data}
   | _ -> raise @@ InterpFatal "set_err not impl"

let lookup t key value_type  =
  let i    = apply_hash t.h1 t.n_buckets key in
  let h2   = oblivious_array_access t.h2s i t.n_buckets in
  let slot = apply_hash h2 t.bucket_size key in
  let addr = i * t.bucket_size + slot in
  let b    = ORAM.read t.oram addr in

  (* TODO: make err oblivious *)
  match from_bytes (pair_ty value_type) b with
  | PairVal{data=(IntVal{value=k;_}, v); _} -> 
    if (k != key) then set_err v 1
    else v
  | _ ->
    raise @@ PerfectHashFatal "could not retrieve"

(* ------------------------------------------------------------------ *)
(* Update                                                               *)
(* ------------------------------------------------------------------ *)

let update t key value =
  let i    = apply_hash t.h1 t.n_buckets key in
  let h2   = oblivious_array_access t.h2s i t.n_buckets in
  let slot = apply_hash h2 t.bucket_size key in
  let addr = i * t.bucket_size + slot in
  ORAM.write t.oram addr (encode_slot ~block_size:t.block_size key value)

(* ------------------------------------------------------------------ *)
(* Tests                                                                *)
(* ------------------------------------------------------------------ *)
 
(* let test () =
  Printf.printf "=== Perfect Hash ORAM tests ===\n%!";
  let make_int v = IntVal{error=0; value=v} in
  let make_pair k v = PairVal{error=0; data=(make_int k, v)} in

  let kvs = ArrayVal{
    error=0;
    length=10;
    data=Array.init 10 (fun i -> make_pair i (make_int (i * 10)))
  } in

  let t = build kvs in

  for i = 0 to 9 do
    assert (lookup t i Ty.INT = Some (make_int (i * 10)))
  done;
  assert (lookup t 99 Ty.INT = None);

  update t 5 (make_int 999);
  assert (lookup t 5 Ty.INT = Some (make_int 999));
  assert (lookup t 4 Ty.INT = Some (make_int 40));

  for _ = 1 to 20 do
    assert (lookup t 3 Ty.INT = Some (make_int 30))
  done;
  Printf.printf "PASS: repeated lookups stable\n%!";

  Printf.printf "All tests passed.\n%!"

let () = test () *)
