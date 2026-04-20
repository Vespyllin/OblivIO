{
  open Parser  
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
}

let nonnewline=[^'\n']
let letter=['a'-'z' 'A'-'Z']
let digit=['0'-'9']
let idchar=letter | digit | '_'

rule token = parse
| [' ' '\t']          { token lexbuf }     (* skip blanks *)
| '\n'                { Lexing.new_line lexbuf; token lexbuf }
| eof                 { EOF }
| ','                 { COMMA }
| ';'                 { SEMICOLON }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '{'                 { LBRACE }
| '}'                 { RBRACE }
| '['                 { LBRACK }
| ']'                 { RBRACK }
| '+'                 { PLUS }
| '-'                 { MINUS }
| '*'                 { TIMES }
| '/'                 { DIVIDE }
| "=="                { EQ }
| "!="                { NEQ }
| "<="                { LE }
| ">="                { GE }
| '<'                 { LT }
| '>'                 { GT }
| '^'                 { CARET }
| ':'                 { COLON }
| "fst"               { FST }
| "snd"               { SND }
| "&&"                { AND }
| "||"                { OR }
| '@'                 { AT }
| '$'                 { DOLLAR }
| "="                 { ASSIGN }
| "?="                { BIND }
| "var"               { VAR }
| "local"             { LOCAL }
| "network"           { NETWORK }
| "channel"           { CHANNEL }
| "size"              { SIZE }
| "oblif"             { OBLIF }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "send"              { SEND }
| "while"             { WHILE }
| "do"                { DO }
| "skip"              { SKIP }
| "int"               { INTTYPE }
| "string"            { STRINGTYPE }
| "ptr"               { PTRTYPE }
| "err"               { ERRTYPE }
| "input"             { INPUT }
| "output"            { OUTPUT }
| "exit"              { EXIT }
| "alloc"             { ALLOC }
| "array"             { ARRAY }
| "read"              { READ }
| "nil"               { NIL }
| "_"                 { UNDERSCORE }
| "??"                { COALESCE }
| "//" nonnewline* '\n' { Lexing.new_line lexbuf; token lexbuf }
| digit+ as i         { match int_of_string_opt i with
                        | Some i' -> INT i'
                        | None -> error lexbuf "Integer too large" }
| digit+ idchar+ as l { error lexbuf @@ "Invalid literal '" ^ l ^ "'" }
| "_" idchar+         { error lexbuf "Invalid identifier, id cannot start with '_'" }
| letter idchar* as id  { ID id }
| '\"'                { let start_p = lexbuf.lex_start_p in
                        let str = string "" lexbuf in
                        lexbuf.lex_start_p <- start_p;
                        STRING str}
| _ as t              { error lexbuf @@ "Invalid token '" ^ (String.make 1 t) ^ "'" }

and string current = parse
| '\"'                { current }
| '\n'                { error lexbuf "Illegal newline in string" }
| '\\' ['\\' '\"' 'n' 't'] as e
                      { string (current^(Scanf.unescaped e)) lexbuf }
| [' '-'~']           { string (current^(Lexing.lexeme lexbuf)) lexbuf }
| eof                 { error lexbuf "Unclosed string at end of file" }
| _ as c              { error lexbuf @@ "Illegal character '" ^ (String.make 1 c) ^ "'" }
