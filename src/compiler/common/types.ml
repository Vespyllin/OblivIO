
module L = Level

type basetype = 
  | INT
  | STRING
  | PAIR of ty * ty
  | ARRAY of ty
  | POINTER of ty
  | PATH of ty * int
  | ERROR 
  | ANY
  | ERR of ty
  | SELF

and ty = Type of {base: basetype; level: L.level}

let base (Type{base;_}) = base
let level (Type{level;_}) = level

let raiseTo (Type{base;level}) pc =
  let level = L.lub level pc in
  Type{base;level}

let rec base_to_string = function
  | INT -> "int"
  | STRING -> "string"
  | PAIR (a,b) ->
    String.concat "" [
      "("
    ; to_string a
    ; ","
    ; to_string b
    ; ")"
    ]
  | ARRAY t -> 
    to_string t ^ "[]"
  | POINTER t -> String.concat "" ["ptr("; to_string t; ")"]
  | PATH (t, s) -> String.concat "" ["path("; to_string t; ")["; string_of_int s; "]"]
  | ERROR -> "error"
  | ERR t -> "err(" ^ base_to_string (base t) ^ ")"
  | ANY -> "any"
  | SELF -> "μ"

and to_string (Type{base;level}) =
  String.concat ""
    [base_to_string base; "@"; L.to_string level]
  
  
