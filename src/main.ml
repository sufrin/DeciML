open Expr
open Value
open Parsing
open Utils

(* Booleans *)

let trueVal = (Tag(0,  "True"))

let falseVal = (Tag(0,  "False"))

let mkBool: bool -> value = function true -> Const trueVal | false -> Const falseVal

(* Primitive Adapters *)

let num2num f = Prim (function 
    | (Const (Num n))  -> Const(Num (f n)) 
    | other            -> semanticError @@ "Expecting a number, got: "^(show_value other))

let num2bool f = Prim (function 
    | (Const (Num n))  -> mkBool (f n) 
    | other            -> semanticError @@ "Expecting a number, got: "^(show_value other))
   
let num2num2num f = Prim (function 
    | (Const (Num n)) -> num2num (fun m -> f n m)
    | other           -> semanticError @@ "Expecting a number, got: "^(show_value other))

let num2num2bool f = Prim (function 
    | (Const (Num n)) -> num2bool (fun m -> (f n m))
    | other           -> semanticError @@ "Expecting a number, got: "^(show_value other))

let con2bool f = Prim (function 
    | (Const n)  -> mkBool (f n)
    | other      -> semanticError @@ "Expecting a constant, got: "^(show_value other))
    
let con2con2bool f = Prim (function 
    | (Const n)  -> con2bool (fun m -> f n m)
    | other      -> semanticError @@ "Expecting a constant, got: "^(show_value other))
    

let globalEnv = ref @@ addLib 
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
    ; ("setMargin",    num2num (fun margin -> Format.set_margin margin; margin))
    ; ("force",        Prim (force (fun v->v)))
    ; ("deepForce",    Prim deepForce)
    ; ("prim_println", Prim(fun v -> Format.fprintf Format.std_formatter "%a\n%!" pp_value v; v))
    ] 
    emptyEnv

let showAst = ref false

let relativePath current path =
let open Filename
in
    if path="" then path else
    if not @@ is_implicit path then path else
    concat (dirname current) path


let rec processPhrase = fun currentPath -> function 
    | Expr ast -> 
           if !showAst then Format.fprintf Format.std_formatter "%a\n%!" pp_expr ast;
           let v = eval None !globalEnv (fun v -> v) ast in
               Format.fprintf Format.std_formatter "@[%a@]\n%!" pp_value v
    | Defs (defs, wheredefs) -> 
                   if !showAst then
                     if wheredefs=[] then
                        Format.fprintf Format.std_formatter  "@[let @[%a@]@];;\n" pp_defs defs 
                     else
                        Format.fprintf Format.std_formatter  "@[let @[%a@]\nwhere @[%a@]@];;\n" pp_defs defs pp_defs wheredefs;
                   let ext   = recBindings !globalEnv wheredefs in
                   let ext'  = recBindings (ext <+> !globalEnv) defs in  
                       if !showEnv then Format.fprintf Format.std_formatter "%a\n%!" pp_layer ext;
                       globalEnv := ext' <+> !globalEnv 
    | EndFile   -> raise EndFile
    | Import paths -> 
             List.iter (fun path -> processArg (relativePath currentPath path)) paths 
    | Notation notations -> ExprLexer.declareNotations notations
    | Nothing   -> ()


and processLexbuf currentPath lexbuf =
  let lexer = ExprLexer.lexer lexbuf in begin
  try
      match parse ~resume:true lexer lexbuf with
      | OK ast         ->  
        (try processPhrase currentPath ast with
        | SemanticError msg -> Format.eprintf "Runtime error: %s\n %!" msg
        | Failure msg       -> Format.eprintf "Syntax error: %s\n%!" msg
        | Stdlib.Sys.Break  -> Format.eprintf "[Interrupted]\n%!" 
        )
      | ERR (pos, msg) ->  
        Format.eprintf "*** %a %s%!"   Utils.pp_fpos pos msg
      | REJECTED -> ()
  with 
  |   (* abandon the current phrase on a lexer error *)
      ExprLexer.LexError (pos, msg) ->
         Format.eprintf "*** Lexing error: %s at %a\n> %!" msg  Utils.pp_fpos pos
  | Stdlib.Sys.Break  -> Format.eprintf "[Interrupted]\n> %!" 
  | SyntaxError   msg -> Format.eprintf "Syntax error: %s\n> %!" msg
  end;
  processLexbuf currentPath lexbuf
  

and processChan path chan =
    let istty  = path="/dev/stdin" || Unix.isatty @@ Unix.descr_of_in_channel chan in
    let lexbuf = Sedlexing.Utf8.from_channel ~chunk_size:(if istty then 1 else 1024) chan in
    Sedlexing.set_filename lexbuf path;
    if istty then
       Sedlexing.set_prompter lexbuf (fun () -> Format.printf "> %!");
    try 
     processLexbuf path lexbuf
    with
     EndFile -> ()
     
and processArg path = 
    match path with
    | "+d" -> Utils.desugarInfix  := true
    | "-d" -> Utils.desugarInfix  := false
    | "+l" -> Utils.idLocs  := true
    | "-l" -> Utils.idLocs  := false
    | "+a" -> showAst := true
    | "+e" -> Utils.showEnv := true
    | "+n" -> ExprLexer.showNotation := true
    | "+m" -> Value.debugMatch := true
    | _    -> try
               let chan = open_in path in processChan path chan
              with
               Sys_error msg -> Format.eprintf "%s\n%!" msg

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





    














