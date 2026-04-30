
module L = Level

type basetype = 
  | INT
  | STRING
  | PAIR of ty * ty
  | ARRAY of ty
  | POINTER of ty
  | PATH of ty * int
  | OMAP of basetype * basetype
  | PMAP of basetype * basetype
  | ANY
  | SELF of ty option ref
  | CRASH 

and ty = Type of {base: basetype; errable: bool; level: L.level}

val base: ty -> basetype
val errable: ty -> bool
val level: ty -> L.level

val raiseTo: ty -> L.level -> ty

val to_string: ty -> string
val base_to_string: basetype -> string
