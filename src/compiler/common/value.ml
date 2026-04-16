
type value =
| IntVal of int
| StringVal of {length: int; data: char array}
| PairVal of value * value
| ArrayVal of {length: int; data: value array}
| PointerVal of {addr: int; cell_size: int}
| ErrVal of {padding: char array; elem_size: int}

let rec to_string = function
  | StringVal {length;data} ->
    "\"" ^ (data |> Array.to_list |> Util.take length |> List.to_seq |> String.of_seq) ^ "\""
  | IntVal n -> Int.to_string n
  | PairVal (a,b) -> String.concat "" [
      "("
    ; to_string a
    ; ","
    ; to_string b
    ; ")"
    ]
  | ArrayVal {length;data} ->
    let datastr =
      data |> Array.to_list
           |> Util.take length
           |> List.map to_string
           |> String.concat ";" in
    "[" ^ datastr ^ "]"
  | PointerVal {addr;cell_size} ->
      "ptr(" ^ string_of_int addr ^ ", " ^ string_of_int cell_size ^ ")" 
  | ErrVal _ ->
      "err"

let rec size = function 
  | IntVal _                          ->    8
  | StringVal{data;_}     ->    8 + Array.length data
  | PairVal (a,b)       ->    size a + size b 
  | ArrayVal {data;  _}  ->    8 + Array.length data
  | ErrVal {padding; _}   ->    8 + Array.length padding
  | PointerVal _                      ->    8