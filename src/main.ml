open Expr
open Value
open Parsing
open Utils

(* Booleans *)

let trueVal  = (Tag(0,  ExprLexer.intern "True"))

let falseVal = (Tag(0,  ExprLexer.intern "False"))



let val_true  = Const trueVal 
and val_false = Const falseVal

let mkBool: bool -> value = function true -> val_true | false -> val_false

(* Primitive Adapters *)

let num2num f = Strict (function 
    | (Const (Num n))  -> (try Const(Num (f n)) with Division_by_zero ->  semanticError @@ "Division by zero")
    | other            -> semanticError @@ "Expecting a number, got: "^(show_value other))

let num2bool f = Strict (function 
    | (Const (Num n))  -> mkBool (f n) 
    | other            -> semanticError @@ "Expecting a number, got: "^(show_value other))
   
let num2num2num f = Strict (function 
    | (Const (Num n)) -> num2num (fun m -> f n m)
    | other           -> semanticError @@ "Expecting a number, got: "^(show_value other))

let num2num2bool f = Strict (function 
    | (Const (Num n)) -> num2bool (fun m -> (f n m))
    | other           -> semanticError @@ "Expecting a number, got: "^(show_value other))

let con2bool f = Strict (function 
    | (Const n)  -> mkBool (f n)
    | other      -> semanticError @@ "Expecting a constant, got: "^(show_value other))
    
let con2con2bool f = Strict (function 
    | (Const n)  -> con2bool (fun m -> f n m)
    | other      -> semanticError @@ "Expecting a constant, got: "^(show_value other))



let globalEnv = ref @@ addLib 
    (List.map (fun (s, v) -> (ExprLexer.intern s, v))
    [ ("prim_is_unit",    Prim (function Tup[] -> val_true | _ -> val_false))
    ; ("prim_untuple",    Prim (function Tup (x::xs) -> Tup[x; Tup xs] 
                               |         other -> Tup[other; unitValue]))
    ; ("prim_succ",       num2num (fun n->n+1))
    ; ("prim_pred",       num2num (fun n->n-1))
    ; ("prim_neg",        num2num (fun n-> -n))
    ; ("prim_add",        num2num2num  (fun n m -> n+m))
    ; ("prim_sub",        num2num2num  (fun n m -> n-m))
    ; ("prim_mul",        num2num2num  (fun n m -> n*m))
    ; ("prim_div",        num2num2num  (fun n m -> n/m))
    ; ("prim_mod",        num2num2num  (fun n m -> n mod m))
    ; ("prim_eq",         num2num2bool (fun n m -> n=m))
    ; ("prim_struct_eq",  Prim (fun l -> Prim (fun r -> mkBool(val_eq l r))))
    ; ("prim_ls",         num2num2bool (fun n m -> n<m))
    ; ("prim_le",         num2num2bool (fun n m -> n<=m))
    ; ("prim_gr",         num2num2bool (fun n m -> n>m))
    ; ("prim_ge",         num2num2bool (fun n m -> n>=m))
    ; ("failWith",        Prim (fun msg -> semanticError @@ ("failWith "^show_value msg)))
    ; ("True",            mkBool true)
    ; ("False",           mkBool false)
    ; ("ref",             Prim(fun v -> Ref(ref v)))
    ; ("set",             Prim (function (Ref r) -> Prim (fun v -> r:=v; v) 
                              |           other -> semanticError @@ "Expecting a reference, got: "^(show_value other)))
    ; ("get",             Prim (function (Ref r) -> !r
                              |           other -> semanticError @@ "Expecting a reference, got: "^(show_value other)))
    ; ("setMargin",       num2num (fun margin -> Format.set_margin margin; margin))
    ; ("force",           Prim (force (fun v->v)))
    ; ("deepForce",       Prim deepForce)
    ; ("prim_println",    Prim(fun v -> Format.fprintf Format.std_formatter "%a@.%!" pp_value v; v))
    ; ("prim_print",      Prim(fun v -> Format.fprintf Format.std_formatter "%a%!" pp_value v; v))
    ; ("prim_nomatch",    Prim(fun _ -> noMatch()))
    ; ("prim_park",       prim_park)
    ; ("prim_unpark",     prim_unpark)
    ; ("prim_runone",     prim_runone)
    ; ("prim_runnable",   prim_runnable)
    ; ("prim_parked",     prim_parked)
    ]) 
    emptyEnv

let showAst = ref false

let relativePath current path =
let open Filename
in
    if path="" then path else
    if dirname current="/dev/" then path else
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
                        Format.fprintf Format.std_formatter  "@[let @[%a@]@];;@." pp_defs defs 
                     else
                        Format.fprintf Format.std_formatter  "@[let @[%a@]\nwhere @[%a@]@];;@." pp_defs defs pp_defs wheredefs;
                   let ext   = recBindings !globalEnv wheredefs in
                   let ext'  = recBindings (ext <+> !globalEnv) defs in  
                       if !showEnv then Format.fprintf Format.std_formatter "%a@."  pp_frame ext';
                       globalEnv := ext' <+> !globalEnv 
    | EndFile   -> raise EndFile
    | Import paths -> 
             List.iter (fun path -> 
                            let path = if isPath path then relativePath currentPath path else path
                            in  processArg path
                       ) paths 
    | Notation notations -> ExprLexer.declareNotations notations
    | Nothing   -> ()


and processLexbuf currentPath lexbuf =
  ExprLexer.setPragmaEval (fun _ text -> processArgs (Str.split (Str.regexp "[ ]+") text));
  let lexer = ExprLexer.lexer lexbuf in begin
  try
      match parse ~resume:true lexer lexbuf with
      | OK ast         ->  
        (try processPhrase currentPath ast with
        | SemanticError msg -> Format.eprintf "Runtime error: %s\n %!" msg
        | Failure msg       -> Format.eprintf "Syntax error: %s\n%!" msg
        | Stdlib.Sys.Break  -> Format.eprintf "[Interrupted]\n%!" 
        | Stack_overflow    -> Format.eprintf "%!\n[Stack Overflow]\n%!" 
        | NoMatch           -> Format.eprintf "%!\n[NoMatch out of context]\n%!" 
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
  Format.pp_print_flush Format.std_formatter ();
  Format.pp_print_flush Format.err_formatter ();  
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
     
and processArgs = function [] -> () | p::ps -> processArg p; processArgs ps

and processArg path = 
    match path with
    | "+d" -> Utils.desugarInfix  := true
    | "-d" -> Utils.desugarInfix  := false
    | "+l" -> Utils.idLocs  := true
    | "-l" -> Utils.idLocs  := false
    | "+a" -> showAst := true
    | "-a" -> showAst := false
    | "+e"  -> Utils.showEnv := true
    | "+ce" -> Utils.showClosureEnv := true
    | "-e"  -> Utils.showEnv := false
    | "-ce" -> Utils.showClosureEnv := false
    | "+n" -> ExprLexer.showNotation := true
    | "-n" -> ExprLexer.showNotation := false
    | "+m" -> Value.debugMatch := true
    | "-m" -> Value.debugMatch := false
    | _    -> 
           if isPath path then 
           let open Filename in
           (* This is where to differentiate compiled module files from source files (eventually) *)
           let path = (try chop_extension path with Invalid_argument _ -> path)^ ".dml" in
               processPath path
           else
               Format.eprintf "[[Unknown switch: %s]]\n%!" path
               
and isPath s = s!="" && s.[0]!='+' && s.[0]!='-'

and processPath path =
    try
        let chan = open_in path in processChan path chan
    with
        Sys_error msg -> Format.eprintf "[[%s]]\n%!" msg


let rec main argv =     
    match argv with
    | []        -> processPath "/dev/stdin"
    | "--"::ps  -> main ps
    | p   ::ps  -> processArg p; main ps


let _ = begin
    Format.set_margin 80;
    Sys.catch_break true; 
    main(List.tl(Array.to_list(Sys.argv)))
end





    


























