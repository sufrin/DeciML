open Expr
open Value
open Parsing

(* Library Primitives *)

let num2num f = Prim (function 
    | (Const (Num n))  -> Const(Num (f n)) 
    | other            -> Fail (show_value other))

let num2bool f = Prim (function 
    | (Const (Num n))  -> Const(Bool (f n)) 
    | other            -> Fail (show_value other))
   
let num2num2num f = Prim (function 
    | (Const (Num n)) -> num2num (fun m -> f n m)
    | other           -> Fail (show_value other))

let num2num2bool f = Prim (function 
    | (Const (Num n)) -> num2bool (fun m -> f n m)
    | other           -> Fail (show_value other))

let con2bool f = Prim (function 
    | (Const n)  -> Const(Bool (f n)) 
    | other      -> Fail (show_value other))
    
let con2con2bool f = Prim (function 
    | (Const n) -> con2bool (fun m -> f n m)
    | other      -> Fail (show_value other))
    
let process lexbuf =
  let lexer = ExprLexer.lexer lexbuf in
  try
      match parse lexer lexbuf with
      | OK ast  ->  
        (match ast with Expr.EndFile -> raise EndFile | _ -> ());
        Format.fprintf Format.std_formatter "%a\n%!" Expr.pp_phrase ast
      | ERR (pos, msg) ->  
        Format.fprintf Format.std_formatter "*** %a %s%!"   Utils.pp_fpos pos msg
  with 
     (* abandon the current phrase on a lexer error *)
     ExprLexer.LexError (pos, msg) ->
         Format.fprintf Format.std_formatter "*** Lexing error: %s at %a\n%!" msg  Utils.pp_fpos pos

let _ =
    let chan   = open_in "/dev/stdin" in
    let istty  = Unix.isatty @@ Unix.descr_of_in_channel chan in
    let lexbuf = Sedlexing.Utf8.from_channel ~chunk_size:(if istty then 1 else 1024) chan in
    Sedlexing.set_filename lexbuf "/dev/stdin";
    if istty then
       Sedlexing.set_prompter lexbuf (fun () -> Format.printf "> %!");
    try 
     while true do process lexbuf done
    with
     EndFile -> ()




