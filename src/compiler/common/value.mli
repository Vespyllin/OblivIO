type value =
  | IntVal of {error: int; value: int}
  | StringVal of {error: int; length: int; data: char array}
  | PairVal of value * value
  | ArrayVal of {error: int; length: int; data: value array}
  | PointerVal of {error: int; addr: int}
  | PathVal of {error: int; addr: int}

val to_string: value -> string

val size: value -> int