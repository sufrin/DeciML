open Format
open Expr
open Utils

type value  = 
 | Const   of con               [@printer pp_con]
 | Tup     of values            [@printer fun fmt vs      -> fprintf fmt "(%a)" (pp_punct_list "," pp_value) vs]
 | Cons    of tag * value       [@printer fun fmt (t, v)  -> fprintf fmt "%a %a" pp_tag t pp_value v]
 | Fun     of env * cases       [@printer fun fmt (e, cs) -> fprintf fmt "\\ %a (in %a)"  pp_cases cs pp_env e]
 | LazyFun of env * case        [@printer fun fmt (e, c)  -> fprintf fmt "\\\\ %a (in %a)"  pp_case c pp_env e]
 | Thunk   of thunk             [@printer fun fmt r       -> fprintf fmt "@@%a" pp_thunk r]
 | Prim    of (value -> value)  [@opaque]
 | Unbound of id                [@printer fun fmt id      -> fprintf fmt "Unbound %s" (show_id id)]
 | Fail    of string            [@printer fun fmt why     -> fprintf fmt "FAIL %s" why]
 [@@deriving show { with_path = false }]

and 
  cont = value -> value        [@opaque]
  [@@deriving show { with_path = false }]
  
and thunk = env * expr * value option ref 
            [@printer fun fmt (env, expr, _)  -> fprintf fmt "%a ~> %a" pp_env env pp_expr expr]
  [@@deriving show { with_path = false }]

and 
  values = value list [@printer pp_punct_list "," pp_value]
  [@@deriving show { with_path = false }]

(* Environments *)

and env = layer list [@printer pp_punct_list "⊕" pp_layer]
 [@@deriving show { with_path = false }]

and layer = 
  | Bind     of bindings        [@printer pp_bindings]
  | Rec      of bindings ref    [@printer (fun fmt bs -> 
                                           let nrbs = !bs in
                                               bs := [];
                                               fprintf fmt "@[REC %a@]" pp_bindings nrbs;
                                               bs := nrbs
                                          )
                                ]
  [@@deriving show { with_path = false }]

and bindings = binding list [@printer pp_punct_list "," pp_binding]
    [@@deriving show { with_path = false }]
  
and binding = (id * value) [@printer fun fmt (i, v) -> fprintf fmt "@[%a=%a@]" pp_id i pp_value v]
    [@@deriving show { with_path = false }]
    
let envDiff layers' layers =
       let rec dropFrom l n =if n<=0 || l==[] then l else dropFrom (List.tl l) (n-1)           
       in dropFrom (List.rev layers') (List.length layers' - List.length layers)
        
let lookup: id -> cont -> env -> value = fun i k e ->
    let rec layers = function 
        | []    -> k(Fail i)
        | l::ls -> match layer l with Some v -> k v | None -> layers ls
        and layer = function
        |  Rec  bs -> bindings !bs
        |  Bind bs -> bindings bs
        and bindings = function 
        |  []                 -> None
        |  (n, v)::_ when n=i -> Some v
        |  _ :: bs'           -> bindings bs'
    in  layers e
   
let bind: id -> value -> env -> env = fun i v e -> Bind [(i, v)]::e

let addBindings: bindings -> env -> env = fun bs e -> Bind bs :: e

let addBinding: id -> value -> bindings -> bindings = fun i v bs -> (i,v)::bs

let emptyEnv: env = []

let emptyBindings: bindings = []

(*    Recursive Environment construction  *)

(* 
    An environment built by extending e with a new empty environment layer, for later knot-tying by recFix 
*)
let recEnv e = Rec(ref emptyBindings) :: e

(*  
    recFix bs env "ties the knot" in env by making the first layer of env refer to bs, providing  
    bs are bindings of variables to values constructed in env. Each value will EMBED env unless
    it is a normal form; so free variable references from it using env will themselves use env.
*)
let recFix bs = function (Rec r :: _ as env) -> (r:=bs; env) | _ -> failwith "recFix at invalid env"

(* Continuation Composition *)

let (>>) f g x = g(f x)


let debuga     = true
let debugMatch = true


(* Pattern matching generates a bindings extension *)

exception NoMatch 
let noMatch () = raise NoMatch

let loop2: ('state->'a->'b->'state) ->  'state -> ('a list * 'b list) -> 'state  = fun f ->
    let rec loop state = function ([], []) -> state | (x::xs, y::ys) -> loop (f state x y) (xs, ys) | _ -> noMatch()
    in  loop

let rec matchPat: pat -> value -> bindings -> bindings = fun p v bs -> 
match p, v with 
| Id i,     _                     -> addBinding i v bs
| Tuple ts, Tup vs                -> loop2 (fun bs' p v -> matchPat p v bs') emptyBindings (ts, vs)
| Con c,    Const c' when c=c'    -> emptyBindings
| _,        _                     -> if debugMatch then eprintf "@." else (); noMatch()


(* Evaluation *)
   
let rec eval: env -> cont -> expr -> value = fun env k -> function
| Id i              -> lookup i k env
| Con c             -> k(Const c)
| Label(name, body) -> eval (bind name (Prim k) env) k body
| Tuple exs         -> evalTuple env (fun vs -> k(Tup (List.rev vs))) [] exs 
| Bra ex            -> eval env k ex         
| Fn defs           -> k(Fun(env, defs))
| LazyFn case       -> k(LazyFun(env, case))
| If (g, e1, e2) ->
     let choose = function
         |  (Const(Bool false)) ->  eval env k e2
         |  _                   ->  eval env k e1
     in
         eval env choose g
|    Ap (rator, rand) ->
        let apply = function
            | Const(Tag t)       ->  eval env (fun v -> k(Cons(t, v))) rand
            | Prim f             ->  eval env (f >> k) rand
            | Fun(defenv, cases) ->  eval env (fun v -> evalCases defenv k v cases) rand
            | LazyFun(defenv, (Id i, body)) ->  
               let env' = bind i (Thunk(defenv, rand, ref None)) env 
               in  eval env' k body
            | other              ->  k(Fail (show_value other))
        in  
            eval env apply rator
|    Apply (l, op, r) ->
        eval env k (Ap(Ap(op, l), r)) 
        (* Runtime desugaring: for convenience in diagnostics *)
|    Let (defs, body) -> 
         let env'       = recEnv env in  
         let evBody ext = eval (recFix ext env') k body in
             evalDefs env' evBody [] defs 
|    At(_, ex) ->    
       eval env k ex         
              
(* |    other -> failwith (show_expr other) *)

and elabRecDefs env defs =
    let env' = recEnv env in
        elabDefs env' (fun ext -> recFix ext env') [] defs

and elabDefs e bindk bindings = function
|   []                -> bindk bindings
|   (pat, expr)::defs -> 
    (* Temporary expedient awaiting generalization of continuation from values to envs *)
    let v = eval e (fun v -> v) expr in
            elabDefs e bindk (matchPat pat v  bindings) defs

(* Evaluates in L-R order, but the order of the result is reversed.
   This preserves linear space and time (via the continuation architecture)
*)
and evalTuple: env -> (values -> value) ->  values -> exprs -> value = fun e k vs -> function
| []       -> k vs
| ex::exs  -> eval e (fun v -> evalTuple e k (v::vs) exs) ex 


and evalDefs: env -> (bindings -> value) -> bindings -> defs -> value = fun e k bindings -> function
|   []                -> k bindings
|   (pat, expr)::defs -> eval e (fun v -> evalDefs e k (matchPat pat v  bindings) defs)  expr


and evalCases: env -> cont -> value -> cases -> value = fun e k v cases -> 
   let rec evalFirst: cases -> value  = function
   |   c::cs         -> (try evalCase e k v c with  NoMatch -> evalFirst cs)
   |   []            -> k(Fail (sprintf "Ran out of cases: %s" (show_value v)))
in evalFirst cases

and evalCase: env -> cont -> value -> def -> value = fun e k v -> function (lhs, rhs) -> 
    let bindings = matchPat lhs v emptyBindings in eval (addBindings bindings e) k rhs 
    
let force k = function
|  Thunk(env, expr, vr) ->
   (match !vr with
   | None   -> eval env (fun v -> vr:=Some v; k v) expr 
   | Some v -> k v
   ) 
|  v -> k v
 






