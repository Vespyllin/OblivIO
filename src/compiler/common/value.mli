type value =
  | IntVal of int
  | StringVal of {length: int; data: char array}
  | PairVal of value * value
  | ArrayVal of {length: int; data: value array}
  | PointerVal of {addr: int; cell_size: int}
  | ErrVal of {padding: char array; elem_size: int}

val to_string: value -> string

val size: value -> int