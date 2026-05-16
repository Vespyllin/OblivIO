module H = Hashtbl

type hash_fn = { a: int; b: int }

type value =
| IntVal of {error: int; value:int}
| StringVal of {error: int; length: int; data: char array}
| PairVal of {error: int; data: (value * value)}
| ArrayVal of {error: int; length: int; data: value array}
| PointerVal of {error: int; addr: int}
| PathVal of {error: int; size: int; addr: int}
| HMapVal of {error: int; a: int; m: int; data: value option array}

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
  | HMapVal _ -> "map"

let rec size = function 
  | IntVal _                                    ->    8
  | StringVal{data;_}               ->    8 + Array.length data
  | PairVal {data=(a,b);_}        ->    8 + size a + size b 
  | ArrayVal {data; _}             ->    8 + Array.fold_left (fun acc v -> acc + size v) 0 data
  | PointerVal _                                ->    8
  | PathVal _                                   ->    8
  | HMapVal {data; _}       ->    8 + 8 + 8 + Array.fold_left (fun acc -> function None -> 8 + acc | Some v -> 8 + acc + size v) 0 data


let set_error (v: value) error : value =
  match v with
  | IntVal {value; _} -> IntVal {error; value}
  | PointerVal {addr; _} -> PointerVal {error; addr}
  | PathVal {size;addr; _} -> PathVal {error; size; addr}
  | StringVal {length; data; _} -> StringVal {error; length; data}
  | ArrayVal {length; data; _} -> ArrayVal {error; length; data}
  | PairVal{data;_} -> PairVal{error; data}
  | HMapVal {a; m; data; _} -> HMapVal {error; a; m; data}

let get_error = function
  | IntVal {error; _} -> error
  | PointerVal {error; _} -> error
  | PathVal {error; _} -> error
  | StringVal {error; _} -> error
  | ArrayVal {error; _} -> error
  | PairVal{error;_} -> error
  | HMapVal {error; _} -> error