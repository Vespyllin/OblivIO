
type value =
  | IntVal of int
  | StringVal of {length: int; data: char array}
  | PairVal of value * value
  | ArrayVal of {length: int; data: value array}
  | NullVal of {length: int; data: char array}


val to_string: value -> string

val size: value -> int