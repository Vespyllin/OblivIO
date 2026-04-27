
module L = Level

type basetype = 
  | INT
  | STRING
  | PAIR of ty * ty
  | ARRAY of ty
  | POINTER of ty
  | PATH of ty * int
  | ANY
  | SELF of ty option ref
  | CRASH 

and ty = Type of {base: basetype; errable: bool; level: L.level}

let base (Type{base;_}) = base
let errable (Type{errable;_}) = errable
let level (Type{level;_}) = level

let raiseTo (Type{base;errable;level}) pc =
  let level = L.lub level pc in
  Type{base;errable;level}

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
  | ANY -> "any"
  | SELF _ -> "μ" 
  | CRASH -> "crash"

and to_string (Type{base;errable;level}) =
  String.concat ""
    [if errable then "err(" else ""; base_to_string base; "@"; L.to_string level; if errable then ")" else "";]
  
  
