
type value =
| IntVal of {error: int; value:int}
| StringVal of {error: int; length: int; data: char array}
| PairVal of value * value
| ArrayVal of {error: int; length: int; data: value array}
| PointerVal of {error: int; addr: int}

let rec to_string = function
  | StringVal {error; length;data} ->
    if error = 1 then "ErrString" else "\"" ^ (data |> Array.to_list |> Util.take length |> List.to_seq |> String.of_seq) ^ "\""
  | IntVal {error; value} -> if error = 1 then "ErrInt" else Int.to_string value
  | PairVal (a,b) -> String.concat "" [
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

let rec size = function 
  | IntVal _                          ->    8
  | StringVal{data;_}     ->    8 + Array.length data
  | PairVal (a,b)       ->    size a + size b 
  | ArrayVal {data;  _}  ->    8 + (8*Array.length data)
  | PointerVal _                      ->    8