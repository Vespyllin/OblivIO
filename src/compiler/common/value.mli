module H = Hashtbl

type hash_fn = { a: int; b: int }


type value =
  | IntVal of {error: int; value: int}
  | StringVal of {error: int; length: int; data: char array}
  | PairVal of {error: int; data: (value * value)}
  | ArrayVal of {error: int; length: int; data: value array}
  | PointerVal of {error: int; addr: int}
  | SPointerVal of {error: int; addr: int}
  | HMapVal of {error: int; a: int; m: int; data: value option array}

val to_string: value -> string

val size: value -> int

val set_error: value -> int -> value
val get_error: value -> int

