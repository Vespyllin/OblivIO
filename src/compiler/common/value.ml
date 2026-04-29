module ORAM = Path_oram

type hash_fn = { a: int; b: int }


type perfect_hash_state =
  { oram        : Path_oram.state
  ; h1          : hash_fn
  ; h2s         : hash_fn array
  ; n_buckets   : int
  ; bucket_size : int
  ; block_size  : int
  }

type value =
| IntVal of {error: int; value:int}
| StringVal of {error: int; length: int; data: char array}
| PairVal of {error: int; data: (value * value)}
| ArrayVal of {error: int; length: int; data: value array}
| PointerVal of {error: int; addr: int}
| PathVal of {error: int; size: int; addr: int}
| MapVal of {error: int; data: perfect_hash_state}

let rec to_string = function
  | StringVal {error; length;data} ->
    if error = 1 then "ErrString" else "\"" ^ (data |> Array.to_list |> Util.take length |> List.to_seq |> String.of_seq) ^ "\""
  | IntVal {error; value} -> if error = 1 then "ErrInt" else Int.to_string value
  | PairVal {error; data=(a,b)} -> 
    if error = 1 then "ErrPair" else
    String.concat "" [
      "("
    ; to_string a
    ; ","
    ; to_string b
    ; ")"
    ]
  | ArrayVal {error; length;data} ->
    if error = 1 then "ErrArr" else
    let datastr =
      data |> Array.to_list
           |> Util.take length
           |> List.map to_string
           |> String.concat ";" in
    "[" ^ datastr ^ "]"
  | PointerVal {error;addr} ->
      if error = 1 then "ErrPtr" else
      "ptr(" ^ string_of_int addr ^ ")" 
  | PathVal {error;size;addr} ->
      if error = 1 then "ErrPtr" else
      "path(" ^ string_of_int addr ^ ")[" ^ string_of_int size ^ "]"
  | MapVal _ -> "map"

let rec size = function 
  | IntVal _                                    ->    8
  | StringVal{data;_}               ->    8 + Array.length data
  | PairVal {data=(a,b);_}        ->    size a + size b 
  | ArrayVal {data;  _}            ->    8 + (8*Array.length data)
  | PointerVal _                                ->    8
  | PathVal _                                   ->    8
  | MapVal _                                    ->    -1