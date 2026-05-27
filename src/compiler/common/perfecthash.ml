
type t = TestMapVal of
  { error: int
  ; a: int
  ; m: int
  ; data: Value.value option array
  }

let hash a m k = ((a * k) land max_int) mod m

(* Oblivious polynomial hash for strings: iterates over all backing array
   slots but only mixes in characters at positions i < length. *)
let hash_string (s: Value.value) : Value.value =
  match s with
  | Value.StringVal {error; length; data} ->
    let h = ref 5381 in
    for i = 0 to Array.length data - 1 do
      let in_len = Bool.to_int (i < length) in
      let c = Char.code data.(i) in
      h := (!h * 33) lxor (in_len * c)
    done;
    let k = (error lxor 1) * !h + error * Int.max_int in
    Value.IntVal {error; value=k}
  | _ -> failwith "hash_string: expected StringVal"

(* Always iterate through all keys to not leak un/successful hash through timing *)
let try_build (keys: Value.value array) m a =
  let seen = Array.make m false in
  let ok = ref true in

  (* Reserve dummy hash location *)
  seen.(hash a m Int.max_int) <- true;
  Array.iter (function
    | Value.IntVal {error; value} ->
      let k = (error lxor 1) * value + error * Int.max_int in
      let h = hash a m k in
      ok := !ok && not (error = 0 && seen.(h));
      seen.(h) <- true
    | Value.StringVal _ as s ->
      (match hash_string s with
      | Value.IntVal {error; value=k} ->
        let h = hash a m k in
        ok := !ok && not (error = 0 && seen.(h));
        seen.(h) <- true
      | _ -> ())
    | _ -> ()
  ) keys;
  !ok

(* Max tries so as to not leak dataset through hashing *)
let max_tries = 1024

let build (arr: Value.value) (dummy: Value.value option) : Value.value =
  let error, pairs = match arr with
    | Value.ArrayVal {error; data; _} -> error, data
    | _ -> failwith "perfecthash: expected ArrayVal"
  in

  let kvs = Array.map (function
    | Value.PairVal {data=((Value.IntVal _ | Value.StringVal _) as k, v); _} -> (k, v)
    | _ -> failwith "perfecthash: expected (int|string, value) pair") pairs in

  let keys = Array.map fst kvs in
  let n = Array.length keys in
  let m = max 1 (n * n) in

  let result = ref None in
  for _ = 1 to max_tries do
    if !result = None then begin
      let a = 1 + Random.int (m - 1) in
      if try_build keys m a then result := Some a
    end
  done;

  let build_error, a = match !result with
    | Some a -> 0, a
    | None   -> 1, 1
  in

  let error = error lor build_error in

  let key_to_int = function
    | Value.IntVal {error; value} -> (error lxor 1) * value + error * Int.max_int
    | Value.StringVal _ as s ->
      (match hash_string s with Value.IntVal {value; _} -> value | _ -> Int.max_int)
    | _ -> Int.max_int
  in

  let data = Array.make m dummy in
  Array.iter (fun (k, v) ->
    data.(hash a m (key_to_int k)) <- Some v
  ) kvs;
  Value.HMapVal { error; a; m; data }

let key_int key =
  match key with
  | Value.IntVal {error; value} -> (error lxor 1) * value + error * Int.max_int
  | Value.StringVal _ as s ->
    (match hash_string s with Value.IntVal {value; _} -> value | _ -> Int.max_int)
  | _ -> failwith "perfecthash: unsupported key type"

let lookup map key =
  match map with
  | Value.HMapVal {a; m; data; _} -> data.(hash a m (key_int key))
  | _ -> failwith "perfecthash: lookup requires HMapVal"

let update map key v =
  match map with
  | Value.HMapVal {a; m; data; _} ->
    let h = hash a m (key_int key) in
    if data.(h) <> None then data.(h) <- Some v
  | _ -> failwith "perfecthash: update requires HMapVal"
