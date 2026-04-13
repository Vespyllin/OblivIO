
module L = Level

type basetype = 
  | INT
  | STRING
  | PAIR of ty * ty
  | ARRAY of ty
  | POINTER of ty
  | ERROR 
  | ANY
  | ERR of ty
  | SELF

and ty = Type of {base: basetype; level: L.level}

val base: ty -> basetype
val level: ty -> L.level

val raiseTo: ty -> L.level -> ty

val to_string: ty -> string
val base_to_string: basetype -> string
