type oper 
  = PlusOp | MinusOp | TimesOp
  | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp 
  | AndOp | OrOp
  | CaretOp | CoalesceOp

val to_string : oper -> string