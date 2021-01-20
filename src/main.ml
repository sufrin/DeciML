open Expr
open Value
open Parsing

(* Booleans *)

let trueVal = (Tag(0,  "True"))

let falseVal = (Tag(1,  "False"))

let mkBool: bool -> value = function true -> Const trueVal | false -> Const falseVal

(* Primitive Adapters *)

let num2num f = Prim (function 
    | (Const (Num n))  -> Const(Num (f n)) 
    | other            -> Fail (show_value other))

let num2bool f = Prim (function 
    | (Const (Num n))  -> mkBool (f n) 
    | other            -> Fail (show_value other))
   
let num2num2num f = Prim (function 
    | (Const (Num n)) -> num2num (fun m -> f n m)
    | other           -> Fail (show_value other))

let num2num2bool f = Prim (function 
    | (Const (Num n)) -> num2bool (fun m -> (f n m))
    | other           -> Fail (show_value other))

let con2bool f = Prim (function 
    | (Const n)  -> mkBool (f n)
    | other      -> Fail (show_value other))
    
let con2con2bool f = Prim (function 
    | (Const n)  -> con2bool (fun m -> f n m)
    | other      -> Fail (show_value other))
    

let globalEnv = ref @@ addBindings 
    [ ("prim_succ",    num2num (fun n->n+1))
    ; ("prim_pred",    num2num (fun n->n-1))
    ; ("prim_add",     num2num2num  (fun n m -> n+m))
    ; ("prim_sub",     num2num2num  (fun n m -> n-m))
    ; ("prim_mul",     num2num2num  (fun n m -> n+m))
    ; ("prim_div",     num2num2num  (fun n m -> n/m))
    ; ("prim_eq",      num2num2bool (fun n m -> n==m))
    ; ("prim_ls",      num2num2bool (fun n m -> n<m))
    ; ("prim_le",      num2num2bool (fun n m -> n<=m))
    ; ("prim_gr",      num2num2bool (fun n m -> n>m))
    ; ("prim_ge",      num2num2bool (fun n m -> n>=m))
    ; ("True",         mkBool true)
    ; ("False",        mkBool false)
    ; ("prim_println", Prim(fun v -> Format.fprintf Format.std_formatter "%a\n%!" pp_value v; v))
    ] 
    emptyEnv

let showAst = ref false
and showEnv = ref false

let processPhrase = function 
    | Expr ast -> 
           if !showAst then Format.fprintf Format.std_formatter "%a\n%!" pp_expr ast;
           let v = eval !globalEnv (fun v -> v) ast in
               Format.fprintf Format.std_formatter "%a\n%!" pp_value v
    | Defs defs -> Format.fprintf Format.std_formatter "%a\n%!" pp_defs defs;
                   let env' = elabRecDefs !globalEnv defs
                   in  
                   let ext = envDiff env' !globalEnv
                   in
                       if !showEnv then Format.fprintf Format.std_formatter "%a\n%!" pp_env ext;
                       globalEnv := env' 
    | EndFile   -> raise EndFile
    | Notation notations -> ExprLexer.declareNotations notations
    | Nothing   -> ()

let rec processLexbuf lexbuf =
  let lexer = ExprLexer.lexer lexbuf in begin
  try
      match parse lexer lexbuf with
      | OK ast         ->  processPhrase ast
      | ERR (pos, msg) ->  
        Format.fprintf Format.std_formatter "*** %a %s%!"   Utils.pp_fpos pos msg
  with 
     (* abandon the current phrase on a lexer error *)
     ExprLexer.LexError (pos, msg) ->
         Format.fprintf Format.std_formatter "*** Lexing error: %s at %a\n%!" msg  Utils.pp_fpos pos
  end;
  processLexbuf lexbuf
  

let processChan path chan =
    let istty  = Unix.isatty @@ Unix.descr_of_in_channel chan in
    let lexbuf = Sedlexing.Utf8.from_channel ~chunk_size:(if istty then 1 else 1024) chan in
    Sedlexing.set_filename lexbuf path;
    if istty then
       Sedlexing.set_prompter lexbuf (fun () -> Format.printf "> %!");
    try 
     processLexbuf lexbuf
    with
     EndFile -> ()
     
let processArg path = 
    match path with
    | "+a" -> showAst := true
    | "+e" -> showEnv := true
    | "+n" -> ExprLexer.showNotation := true
    | _ -> let chan = open_in path in processChan path chan

let rec main argv =     
    match argv with
    | []        -> processArg "/dev/stdin"
    | "--"::ps  -> main ps
    | p   ::ps  -> processArg p; main ps


let _ = begin
    Format.set_margin 80;
    Sys.catch_break true; 
    main(List.tl(Array.to_list(Sys.argv)))
end





    









