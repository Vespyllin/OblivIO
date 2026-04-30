module H = Hashtbl

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
  | IntVal of {error: int; value: int}
  | StringVal of {error: int; length: int; data: char array}
  | PairVal of {error: int; data: (value * value)}
  | ArrayVal of {error: int; length: int; data: value array}
  | PointerVal of {error: int; addr: int}
  | PathVal of {error: int; size: int; addr: int}
  | OMapVal of {error: int; data: perfect_hash_state}
  | PMapVal of {error: int; data: (int, value) H.t}

val to_string: value -> string

val size: value -> int