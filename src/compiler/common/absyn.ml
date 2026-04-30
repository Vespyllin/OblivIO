type pos = Lexing.position 

module T = Types
module L = Level
module Ch = Channel
include Oper

type program = Prog of { node: string; decls: decl list; hls: hl list }
and decl
  = VarDecl of { ty: T.ty; x: string; init: exp; pos: pos }
  | NetworkChannelDecl of { channel: Ch.channel; level: L.level; potential: int; ty: T.ty; pos: pos }
  | LocalChannelDecl of { ch: string; ty: T.ty; pos: pos }
and hl
  = Hl of { handler: string; level: L.level; potential: int; x: string; ty: T.ty; body: cmd; pos: pos }
and var = Var of { var_base: var_base; pos: pos}
and var_base
  = SimpleVar of string
  | SubscriptVar of {var: var; exp: exp}
  | MapVar of {var: var; exp: exp}
  | HeapVar of { var: var }

and exp = Exp of { exp_base: exp_base; pos: pos }
and proj
  = Fst
  | Snd
and exp_base
  = IntExp of int
  | StringExp of string
  | NilExp
  | OnilExp of int
  | VarExp of var
  | ProjExp of {proj: proj; exp:exp}
  | SizeExp of exp
  | OpExp of { left: exp; oper: oper; right: exp }
  | PairExp of (exp*exp)
  | ArrayExp of exp list
  | ArrayConstructorExp of {value: exp; length: int}
  | OMapExp of exp list
  | PMapExp of exp list
  | AllocExp of exp
  | OramExp of {value: exp; size: int}


and cmd = Cmd of { cmd_base: cmd_base; pos: pos }
and cmd_base
  = SkipCmd
  | SeqCmd of { c1: cmd; c2: cmd }
  | AssignCmd of { var: var; exp: exp }
  | BindCmd of { var: var; exp: exp }
  | InputCmd of { var: var; ch: string; size: exp }
  | OutputCmd of { ch: string; exp: exp }
  | SendCmd of { channel: Ch.channel; exp: exp }
  | IfCmd of { test: exp; thn: cmd; els: cmd }
  | WhileCmd of { test: exp; body: cmd }
  | OblivIfCmd of { test: exp; thn: cmd; els: cmd }
  | ExitCmd

 