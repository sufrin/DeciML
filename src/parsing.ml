(* All the application-specific dependencies of Parsing are here *)
module Syntax = 
struct
  (* the type of abstract syntax tree *)
  type tree          = Expr.phrase
  
  (* fetch the error message corresponding to a parse automaton state number *)
  let  errorMessage = ExprParserMessages.message
  
  (* the initial parser state *)
  let  initialState  = ExprParser.Incremental.phrase
  
  (* the parser interpreter module, implementing the specialized
     abstract type of parser state for this syntax
  *)
  module Interpreter = ExprParser.MenhirInterpreter
end

(* Parsing logic *)

module I = Syntax.Interpreter
module S = MenhirLib.General

type parserState = Syntax.tree I.checkpoint

(* Current starting position of symbol in lexbuf *) 
let currentPos lexbuf = fst @@ Sedlexing.lexing_positions lexbuf

(* Starting state for incremental parser using this lexbuf at its current position *)
let initialState lexbuf: parserState = 
    Syntax.initialState @@ currentPos lexbuf

(* State number of the current parse state *)
let stateNumber env: int =
  match Lazy.force (I.stack env) with
  | S.Nil   -> 0 (* The stack is empty, the parser is in its initial state, whose  number is 0. *) 
  | S.Cons (Element (s, _, _, _), _) -> I.number s


let shortMessages = ref true (******** replace when grammar stabilises *********)

(* Error message corresponding to the current (error) state *)
let errorMessage env =
    let state = stateNumber env in
    if !shortMessages then 
       Format.sprintf "Syntax error (in state [%d])\n" state
    else
    match Syntax.errorMessage state with
    | exception Not_found -> Format.sprintf "[%d] Syntax error\n" state (* for some unknown reason the auton generated messages all have \n at the end *)
    | msg                 -> Format.sprintf "[%d] %s" state msg
    
exception EndFile

type ('a, 'b) result = OK of 'a | ERR of 'b | REJECTED

(* A parser that returns one of OK tree or ERR (position, message) and doesn't
   try to recover from an error 

let rec parser lexer lexbuf (parserState: parserState) =
    match parserState with
    | I.InputNeeded   _   -> parser lexer lexbuf @@ I.offer parserState (lexer())
    | I.Shifting      _ 
    | I.AboutToReduce _   -> parser lexer lexbuf @@ I.resume parserState
    | I.HandlingError env -> ERR(currentPos lexbuf, errorMessage env)
    | I.Accepted ast      -> OK ast
    | I.Rejected          -> assert false (* errors already terminate the parser *)

*)


let reportERR(pos, message) = Format.eprintf "*** %a %s%!"  Utils.pp_fpos pos message

let parser resume report lexer lexbuf (parserState: parserState) =
  let rec parse (parserState: parserState) =
    match parserState with
    | I.InputNeeded   _   -> parse @@ I.offer parserState (lexer())
    | I.Shifting      _ 
    | I.AboutToReduce _   -> parse @@ I.resume parserState
    | I.HandlingError env -> 
        if resume then begin
           report(currentPos lexbuf, errorMessage env); 
           parse @@ I.resume ~strategy:`Simplified parserState
        end else
           ERR(currentPos lexbuf, errorMessage env)
    | I.Accepted ast      -> OK ast
    | I.Rejected          -> REJECTED
   in
      parse parserState

let parse ?(resume = false) ?(report = reportERR) lexer lexbuf = parser resume report lexer lexbuf (initialState lexbuf)



