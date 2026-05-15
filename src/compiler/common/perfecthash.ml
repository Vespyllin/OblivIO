
type t = TestMapVal of
  { error: int
  ; a: int
  ; m: int
  ; data: Value.value option array
  }

let hash a m k = ((a * k) land max_int) mod m

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
    | _ -> ()
  ) keys;
  !ok

(* Max tries so as to not leak dataset through hashing *)
let max_tries = 1024

let build (arr: Value.value) : t =
  let error, pairs = match arr with
    | Value.ArrayVal {error; data; _} -> error, data
    | _ -> failwith "perfecthash: expected ArrayVal"
  in

  let kvs = Array.map (function
    | Value.PairVal {data=(Value.IntVal _ as k, v); _} -> (k, v)
    | _ -> failwith "perfecthash: expected (int, value) pair") pairs in

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

  let data = Array.make m None in
  Array.iter (function
    | (Value.IntVal {error; value}, v) ->
      let k = (error lxor 1) * value + error * Int.max_int in
      data.(hash a m k) <- Some v
    | _ -> ()) kvs;
  TestMapVal { error; a; m; data }

let lookup (TestMapVal {a; m; data; _}) = function
  | Value.IntVal {error; value} ->
    let k = (error lxor 1) * value + error * Int.max_int in
    data.(hash a m k)
  | _ -> failwith "perfecthash: lookup key must be IntVal"

let update (TestMapVal {a; m; data; _}) key v = match key with
  | Value.IntVal {error; value} ->
    let k = (error lxor 1) * value + error * Int.max_int in
    let h = hash a m k in
    if data.(h) <> None then data.(h) <- Some v
  | _ -> failwith "perfecthash: update key must be IntVal"
