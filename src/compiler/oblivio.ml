exception CompileError

module Tr = Common.Trace

type config = {file:string; unsafe:bool; print_when: Tr.print_when; print_what: Tr.print_what}

let initLexer filename = 
  let input = open_in filename in
  let filebuf = Lexing.from_channel input in
  filebuf.lex_curr_p <- { filebuf.lex_curr_p with pos_fname = filename };  
  (input, filebuf)

let parse file = 
  let input, filebuf = initLexer file in 
  let parseRes = 
    try Parser.program Lexer.token filebuf
    with
    | Lexer.Error msg -> Printf.eprintf "%s%!" msg; raise CompileError
    | Parser.Error ->  
      let pos1 = Lexing.lexeme_start_p filebuf in
      let pos2 = Lexing.lexeme_end_p filebuf in
      let lexeme = Lexing.lexeme filebuf in
      Printf.fprintf stderr "%s:%d:%d - %d:%d: syntax error '%s'\n"
        pos1.pos_fname pos1.pos_lnum (pos1.pos_cnum - pos1.pos_bol)
        pos2.pos_lnum (pos2.pos_cnum - pos2.pos_bol + 1)
        lexeme;
      raise CompileError
  in 
  close_in input;
  parseRes

let semant prog =
  let success, res = Semant.transProg prog in
  if success
  then res
  else raise CompileError

let interp unsafe print_when print_what prog =
  Interpreter.Interp.interp ~unsafe print_when print_what prog
  
let client {file;unsafe;print_when;print_what} =
  let exitCode = ref 0 in
  
  begin 
    try
      parse file
      |> semant
      |> interp unsafe print_when print_what
    with
      CompileError -> (exitCode := 1)
  end;
  exit (!exitCode)

open Cmdliner

let src_arg =
  let doc = "Source file $(docv)." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let unsafe_arg =
  let doc = "Disable padding and oblivious branching and run the program in an $(docv) mode." in
  Arg.(value & flag & info ["u";"unsafe"] ~docv:"UNSAFE" ~doc)

let print_when_arg =
  let ls = [("onthefly", Tr.ONTHEFLY); ("atexit", Tr.ATEXIT)] in
  let doc = "Print $(docv) ." in
  Arg.(value & opt (enum ls) Tr.ATEXIT & info ["p";"print"] ~docv:"TRACE" ~doc)

let print_what_arg =
  let ls = [("nothing", Tr.NOTHING); ("aggregate", Tr.AGGREGATE); ("full", Tr.FULL)] in
  let doc = "Print $(docv) ." in
  Arg.(value & opt (enum ls) Tr.NOTHING & info ["v";"verbosity"] ~docv:"VERBOSE" ~doc)

let check file unsafe print_when print_what =
  if Filename.extension file |> String.equal ".json"
  then Interpreter.Server.start file
  else client {file;unsafe;print_when;print_what}

let main_t =
  Term.(const check $ src_arg $ unsafe_arg $ print_when_arg $ print_what_arg)

let info =
  let doc = "OblivIO interpreter." in
  Cmd.info "OblivIO" ~version:"v0.5" ~doc ~exits:Cmd.Exit.defaults

let _ = 
  Cmd.v info main_t |> Cmd.eval |> exit