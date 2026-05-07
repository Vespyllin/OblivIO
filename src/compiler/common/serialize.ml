open Value

module Ty = Types

exception SerializeFatal of string

let rec get_byte_size (v: value) : int =
  let fixed_size = 3+8 in
  match v with
  | IntVal _ -> fixed_size
  | PointerVal _ -> fixed_size
  | PathVal _ -> fixed_size
  | PairVal {data=(a,b);_} -> 3 + get_byte_size a + get_byte_size b
  | StringVal {data; _} -> 3 + Array.length data
  | ArrayVal {data; _} -> 3 + Array.length data * fixed_size
  | _ -> raise @@ SerializeFatal "get_byte_size not impl"

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
    let total = 3 + Bytes.length v1d + Bytes.length v2d in
    let b = Bytes.make total '\x00' in
    Bytes.set_uint8 b 0 6;
    Bytes.set_uint8 b 1 error;
    Bytes.blit v1d 0 b 3 (Bytes.length v1d);
    Bytes.blit v2d 0 b (3 + (Bytes.length v1d)) (Bytes.length v2d);
    b
  | _ -> raise @@ SerializeFatal "to_bytes: unsupported value type"

let rec from_bytes (target_type: Ty.basetype) (b: bytes) : value =
  let tag = Bytes.get_uint8 b 0 in
  let error = Bytes.get_uint8 b 1 in
  match target_type with
  | Ty.INT ->
    let value = Int64.to_int (Bytes.get_int64_be b 3) in
    let error = error lor (Bool.to_int (tag <> 1)) in
    IntVal {error; value}
  | Ty.PATH (_, s) ->
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
    let available_elems = (Bytes.length b - 3) / 11 in
    let data = Array.init available_elems (fun i -> from_bytes (Ty.base inner_ty) (Bytes.sub b (3 + i * 11) 11)) in
    let error = error lor (Bool.to_int (tag <> 5)) in
    ArrayVal {error; length; data}
  | Ty.PAIR (v1, v2) ->
    let error = error lor (Bool.to_int (tag <> 6)) in
    let v1d = from_bytes (Ty.base v1) (Bytes.sub b 3 (Bytes.length b - 3)) in
    let v1_size = get_byte_size v1d in
    let v2d = from_bytes (Ty.base v2) (Bytes.sub b (3 + v1_size) (Bytes.length b - (3 + v1_size))) in
    PairVal {error; data=(v1d,v2d)}
  | Ty.SELF t -> 
    begin match !t with
    | Some x -> from_bytes (Ty.base x) b
    | None -> raise @@ SerializeFatal "uninitialized recursive type";
    end
  | _ -> raise @@ SerializeFatal ("from_bytes: unsupported target type " ^ (Ty.base_to_string target_type))