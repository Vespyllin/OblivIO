%{
  open Common.Absyn
  module L = Common.Level
  module T = Common.Types
  module Ch = Common.Channel
%}

%token EOF
%token <string> ID
%token <int> INT
%token <string> STRING
%token VAR CHANNEL LOCAL NETWORK
%token SEMICOLON COMMA
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE CARET
%token FST SND DOLLAR
%token COLON SIZE AT EXIT 
%token AND OR ASSIGN BIND IF THEN ELSE WHILE DO
%token SKIP OBLIF SEND INPUT OUTPUT
%token INTTYPE STRINGTYPE
%token PTRTYPE ERRTYPE UNDERSCORE PATHTYPE
%token ALLOC ORAM ARRAY NIL ONIL
%token COALESCE

%left OR
%left AND
%left COALESCE
%nonassoc EQ NEQ GT LT GE LE
%left CARET
%left PLUS MINUS
%left TIMES
%right FST SND
%nonassoc UMINUS

%start <Common.Absyn.program> program  

%%
%inline paren(X): LPAREN x=X RPAREN { x }
%inline brace(X): LBRACE x=X RBRACE { x }
%inline brack(X): LBRACK x=X RBRACK { x }
%inline slist(SEP,X): l=separated_list(SEP,X) { l }
%inline spair(X,SEP,Y): p=separated_pair(X,SEP,Y) { p }

(* binop *)
%inline op:
| PLUS      { PlusOp }
| MINUS     { MinusOp }
| TIMES     { TimesOp }
| AND       { AndOp }
| OR        { OrOp }
| EQ        { EqOp }
| NEQ       { NeqOp }
| LT        { LtOp }
| LE        { LeOp }
| GT        { GtOp }
| GE        { GeOp }
| CARET     { CaretOp }
| COALESCE  { CoalesceOp }

binop_exp:
| MINUS right=exp %prec UMINUS
  { OpExp{left=Exp{exp_base=IntExp 0;pos=$startpos}; oper=MinusOp; right} }
| left=exp oper=op right=exp
  { OpExp{left; oper; right} }

lvl:
| ls=brace(slist(COMMA,ID))   { L.of_list ls }

var_base:
| x=ID { SimpleVar x}
| var=var exp=brack(exp)
  { SubscriptVar {var;exp} }
| TIMES var=var
  { HeapVar {var} }

var:
| var_base=var_base { Var {var_base; pos=$startpos} }

(* Expressions *)
exp_base:
| i=INT             { IntExp i }
| s=STRING          { StringExp s }
| NIL               { NilExp }
| v=var             { VarExp v }
| SIZE e=paren(exp) { SizeExp e }
| e=binop_exp       { e }
| FST exp=exp       { ProjExp {proj=Fst; exp} }
| SND exp=exp       { ProjExp {proj=Snd; exp} }
| ONIL i=INT        { OnilExp i }
| pair=paren(spair(exp,COMMA,exp))
  { PairExp pair }
| arr=brack(slist(SEMICOLON,exp))
  { ArrayExp arr}
| ARRAY LPAREN length=INT COMMA value=exp RPAREN
  { ArrayConstructorExp {value;length}}
| ALLOC exp=exp
  { AllocExp exp }
| ORAM LPAREN exp=exp COMMA size=INT RPAREN
  { OramExp{value=exp;size} }

exp:
| e=exp_base          { Exp {exp_base=e; pos=$startpos} }
| e=paren(exp_base)   { Exp {exp_base=e; pos=$startpos} }

cmd_base_seq:
| c=cmd_base
  { c }
| c1=cmd_base c2=cmd_seq
  { SeqCmd {c1=Cmd {cmd_base=c1; pos=$startpos};c2} }

cmd_base:
| v=var ASSIGN e=exp SEMICOLON
  { AssignCmd{var=v; exp=e} }
| v=var BIND e=exp SEMICOLON
  { BindCmd{var=v; exp=e} }
| SKIP SEMICOLON
  { SkipCmd }
| IF test=exp THEN thn=cmd ELSE els=cmd
  { IfCmd{test; thn; els} }
| OBLIF test=exp THEN thn=cmd ELSE els=cmd
  { OblivIfCmd{test; thn; els} }
| WHILE test=exp DO body=cmd
  { WhileCmd{test; body} }
| var=var BIND INPUT LPAREN ch=ID COMMA size=exp RPAREN SEMICOLON
  { InputCmd {var;ch;size} }
| OUTPUT LPAREN ch=ID COMMA exp=exp RPAREN SEMICOLON
  { OutputCmd{ch;exp} }
| SEND LPAREN channel=channel COMMA exp=exp RPAREN SEMICOLON
  { SendCmd{channel;exp} }
| EXIT LPAREN RPAREN SEMICOLON
  { ExitCmd }

cmd_seq:
| c=cmd_base_seq
  { Cmd {cmd_base=c; pos=$startpos} }

cmd:
| c=cmd_base
  { Cmd {cmd_base=c; pos=$startpos} }
| c=brace(cmd_base_seq)
  { Cmd {cmd_base=c; pos=$startpos} }

basetype:
| INTTYPE
  { T.INT }
| STRINGTYPE
  { T.STRING }
| LPAREN t1=type_at_lvl TIMES t2=type_at_lvl RPAREN
  { T.PAIR (t1,t2) }
| t=type_at_lvl LBRACK RBRACK
  { T.ARRAY t }
| PTRTYPE LPAREN t=type_at_lvl RPAREN
  { T.POINTER t }
| PATHTYPE LPAREN t=type_at_lvl RPAREN LBRACK s=INT RBRACK
  { T.PATH (t, s) }

%inline type_at_lvl:
| base=basetype AT level=lvl  { T.Type{base;level} }
| UNDERSCORE                  { T.Type{base=T.SELF; level=L.bottom} }

%inline type_anno:
| COLON t=type_at_lvl  { t }
| COLON ERRTYPE LPAREN t=type_at_lvl RPAREN { T.Type{base=T.ERR t; level=L.bottom} }


channel:
| node=ID DIVIDE handler=ID
  { Ch.Ch {node;handler} }

potential:
| 
  { 0 }
| DOLLAR p=INT
  { p }

decl:
| VAR x=ID ty=type_anno ASSIGN init=exp SEMICOLON
  { VarDecl {ty; x; init; pos=$startpos} }
| NETWORK CHANNEL channel=channel AT level=lvl potential=potential ty=type_anno SEMICOLON
  { NetworkChannelDecl {ty; level; channel; potential; pos=$startpos(channel)} }
| LOCAL CHANNEL ch=ID ty=type_anno SEMICOLON
  { LocalChannelDecl {ch; ty; pos=$startpos} }

handler:
| handler=ID AT level=lvl potential=potential LPAREN x=ID ty=type_anno RPAREN LBRACE body=cmd_seq RBRACE
  { Hl {handler;potential;x;ty;level;body;pos=$startpos(handler)} }

(* Top-level *)
program:
| node=ID decls=decl* hls=handler* EOF
  { Prog {node;decls;hls} }
