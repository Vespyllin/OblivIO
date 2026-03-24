module A = Common.Absyn
module Err = Errorenv
module Ty = Common.Types
module L = Common.Level
module Ch = Common.Channel
module H = Hashtbl
type context = {
  gamma : (string, Ty.ty) H.t;
  lambda : (Ch.channel, L.level * Ty.ty * int) H.t;
  delta : (string, Ty.ty) H.t;
  pi : (string, Ty.ty) H.t;
  err : Err.errorenv;
}
val _bot : Ty.basetype -> Ty.ty
val raiseTo : Common.Types.ty -> L.level -> Common.Types.ty
val errLvl : Err.errorenv -> Lexing.position -> string -> L.level
val errTy : Err.errorenv -> Lexing.position -> string -> Ty.ty
val lookupVar :
  context -> string -> Lexing.position -> Common.Tabsyn.varloc * Ty.ty
val lookupInternal : context -> string -> Lexing.position -> Ty.ty
val lookupRemote :
  context -> Ch.channel -> Lexing.position -> L.level * Ty.ty * int
val e_ty : Common.Tabsyn.exp -> Common.Tabsyn.exp * Common.Types.ty
val e_ty_lvl :
  Common.Tabsyn.exp -> Common.Tabsyn.exp * Common.Types.ty * Ty.L.level
val v_ty : Common.Tabsyn.var -> Common.Tabsyn.var * Common.Types.ty
val v_ty_loc :
  Common.Tabsyn.var ->
  Common.Tabsyn.var * Common.Types.ty * Common.Tabsyn.varloc
val v_ty_lvl :
  Common.Tabsyn.var ->
  Common.Tabsyn.var * Common.Types.ty * Common.Level.level
val v_ty_lvl_loc :
  Common.Tabsyn.var ->
  Common.Tabsyn.var * Common.Types.ty * Common.Level.level *
  Common.Tabsyn.varloc
val isSameBase : Ty.ty -> Ty.ty -> bool
val checkBaseType : Ty.ty -> Ty.ty -> Err.errorenv -> Lexing.position -> unit
val checkFlow : L.level -> L.level -> Err.errorenv -> Lexing.position -> unit
val checkFlowType : Ty.ty -> Ty.ty -> Err.errorenv -> Lexing.position -> unit
val checkComparable :
  Common.Types.ty ->
  Common.Types.ty -> Err.errorenv -> Lexing.position -> unit
val checkAssignable :
  Ty.ty -> Ty.ty -> Err.errorenv -> Lexing.position -> unit
val checkLowPC : L.level -> Err.errorenv -> Lexing.position -> unit
val checkInt : Ty.ty -> Err.errorenv -> Lexing.position -> unit
val checkString : Ty.ty -> Err.errorenv -> Lexing.position -> unit
exception NotImplemented of string
val transExp : context -> A.exp -> Common.Tabsyn.exp
val transVar : context -> A.var -> Common.Tabsyn.var
val varname : Common.Tabsyn.var -> string
val transCmd : context -> L.level -> int -> A.cmd -> Common.Tabsyn.cmd * int
val transDecl : context -> A.decl -> Common.Tabsyn.decl
val transHl : context -> string -> A.hl -> Common.Tabsyn.hl
val transProg : A.program -> bool * Common.Tabsyn.program
