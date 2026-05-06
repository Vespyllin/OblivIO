(* Perfect Hashing over Path RustOram
   Keys are known at build time (runtime).
   Uses two-level perfect hashing with fixed-size padded buckets
   so bucket sizes are never observable. *)

open Value

module RustOram = ORAM.Rust_oram
module Ty   = Types
module L    = Level
module S    = Serialize

exception PerfectHashFatal of string

let large_prime = 1000003
let max_tries   = 64

let make_hash () =
  { a = 1 + Random.int (large_prime - 1)
  ; b = Random.int large_prime
  }

let apply_hash h m key =
  abs ((h.a * key + h.b) mod large_prime) mod m

let int_ty = Ty.Type{base=Ty.INT; errable=false; level=L.bottom}
let pair_ty vt = Ty.PAIR (int_ty, Ty.Type{base=vt; errable=false; level=L.bottom})

let encode_slot ~block_size key value : bytes =
  let pair = PairVal{error=0; data=(IntVal{error=0; value=key}, value)} in
  let vb   = S.to_bytes pair in
  let b    = Bytes.make block_size '\x00' in
  Bytes.blit vb 0 b 0 (min (Bytes.length vb) block_size);
  b

let decode_slot vt (b: bytes) : (int * value) option =
  if Bytes.get_uint8 b 0 = 0 then None
  else
    match S.from_bytes (pair_ty vt) b with
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

  let block_size = Array.fold_left (fun acc v -> max acc (S.get_byte_size v)) 0 kvs_arr in

  let capacity =
    let total = n_buckets * bucket_size in
    let p = ref 4 in
    while !p < total do p := !p * 2 done;
    !p
  in

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

  (* Create Rust RustOram — capacity and block_size as separate args *)
  let oram = RustOram.create capacity block_size in

  (* Fill with dummies *)
  for addr = 0 to n_buckets * bucket_size - 1 do
    RustOram.write oram addr (dummy_block block_size)
  done;

  (* Write each KV pair *)
  for j = 0 to n - 1 do
    let k, pair = match kvs_arr.(j) with
      | PairVal{data=(IntVal{value=k;_}, _);_} as p -> k, p
      | _ -> raise @@ PerfectHashFatal "map elements must be pairs with int keys" in
    let target_i = apply_hash h1 n_buckets k in
    let h2       = oblivious_array_access h2s target_i n_buckets in
    let slot     = apply_hash h2 bucket_size k in
    let addr     = target_i * bucket_size + slot in
    let b        = Bytes.make block_size '\x00' in
    let vb       = S.to_bytes pair in
    Bytes.blit vb 0 b 0 (min (Bytes.length vb) block_size);
    RustOram.write oram addr b
  done;

  { oram; h1; h2s; n_buckets; bucket_size; block_size }

let lookup t key value_type =
  let i    = apply_hash t.h1 t.n_buckets key in
  let h2   = oblivious_array_access t.h2s i t.n_buckets in
  let slot = apply_hash h2 t.bucket_size key in
  let addr = i * t.bucket_size + slot in
  let b    = RustOram.read t.oram addr in
  match S.from_bytes (pair_ty value_type) b with
  | PairVal{data=(IntVal{value=k;_}, v); _} ->
    if (k != key) then set_error v 1
    else v
  | _ ->
    raise @@ PerfectHashFatal "could not retrieve"

let update t key value =
  let i    = apply_hash t.h1 t.n_buckets key in
  let h2   = oblivious_array_access t.h2s i t.n_buckets in
  let slot = apply_hash h2 t.bucket_size key in
  let addr = i * t.bucket_size + slot in
  RustOram.write t.oram addr (encode_slot ~block_size:t.block_size key value)