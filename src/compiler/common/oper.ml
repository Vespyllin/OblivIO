type oper 
  = PlusOp | MinusOp | TimesOp
  | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp 
  | AndOp | OrOp
  | CaretOp | CoalesceOp

  let to_string = function
    | PlusOp -> "+"
    | MinusOp -> "-"
    | TimesOp -> "*"
    | EqOp -> "="
    | NeqOp -> "<>"
    | LtOp -> "<"
    | LeOp -> "<="
    | GtOp -> ">"
    | GeOp -> ">="
    | AndOp -> "and"
    | OrOp -> "or"
    | CaretOp -> "^"
    | CoalesceOp -> "??"