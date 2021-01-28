open Format
open Expr
open Utils

let shortenEnv e = if !Utils.showEnv then e else []

type value  = 
 | Const   of con               [@printer fun fmt c       -> fprintf fmt "%a" pp_con c]
 | Tup     of values            [@printer fun fmt vs      -> fprintf fmt "@[(%a)@]" (pp_punct_list "," pp_value) vs]
 | Cons    of tag * values      [@printer pp_cons pp_value]
 | Fun     of env * cases       [@printer fun fmt (e, cs) -> fprintf fmt "@[\\ (%a)\n(in %a)@]"  pp_cases cs pp_env (shortenEnv e)] 
 | LazyFun of env * case        [@printer fun fmt (e, c)  -> fprintf fmt "@[\\\\ %a\n(in %a)@]"  pp_case c pp_env (shortenEnv e)] 
 | Thunk   of thunk             [@printer pp_thunk]
 | Prim    of (value -> value)  [@opaque]
 | Unbound of id                [@printer fun fmt id      -> fprintf fmt "Unbound %s" (show_id id)]
 | Fail    of string            [@printer fun fmt why     -> fprintf fmt "FAIL %s" why]
 [@@deriving show { with_path = false }]

and 
  cont = value -> value        [@opaque]
  [@@deriving show { with_path = false }]
  
and thunk = env * expr * value option ref 
            [@printer fun fmt (env, expr, v)  -> fprintf fmt "%a%a" 
                                                             pp_env (shortenEnv env) 
                                                             (pp_th pp_expr pp_value) (expr, !v)]
  [@@deriving show { with_path = false }]

and 
  values = value list [@printer pp_punct_list "," pp_value]
  [@@deriving show { with_path = false }]

(* Environments *)

and env = layer list [@printer pp_punct_list "⊕" pp_layer]
 [@@deriving show { with_path = false }]

and layer = 
  | Lib      of bindings        [@printer fun fmt bs -> fprintf fmt "<library>"]
  | Bind     of bindings        [@printer pp_bindings]
  | Rec      of bindings ref    [@printer (fun fmt bs -> 
                                           let nrbs = !bs in
                                               bs := [];
                                               fprintf fmt "REC %a" pp_bindings nrbs;
                                               bs := nrbs
                                          )
                                ]
  [@@deriving show { with_path = false }]

and bindings = binding list [@printer pp_punct_list "," pp_binding]
    [@@deriving show { with_path = false }]
  
and binding = (id * value) [@printer fun fmt (i, v) -> fprintf fmt "@[%a=%a@]" pp_id i pp_value v]
    [@@deriving show { with_path = false }]
            
let lookup: location option -> id -> cont -> env -> value = fun loc i k e ->
    let rec layers = function 
        | []    -> semanticError @@ (Format.sprintf "Unbound variable: %s %s" i (match loc with None -> "" | Some l -> Utils.show_location l))
        | l::ls -> match layer l with Some v -> k v | None -> layers ls
        and layer = function
        |  Rec  bs -> bindings !bs
        |  Bind bs -> bindings bs
        |  Lib bs  -> bindings bs
        and bindings = function 
        |  []                 -> None
        |  (n, v)::_ when n=i -> Some v
        |  _ :: bs'           -> bindings bs'
    in  layers e

let (<+>) layer env  = layer :: env
   
let bind: id -> value -> env -> env = fun i v e -> Bind [(i, v)]::e

let addBindings: bindings -> env -> env = fun bs e -> Bind bs :: e

let addLib: bindings -> env -> env = fun bs e -> Lib bs :: e

let addBinding: id -> value -> bindings -> bindings = fun i v bs -> (i,v)::bs

let emptyEnv: env = []

let emptyBindings: bindings = []

(*    Recursive Environment construction  *)

(* 
    An environment built by extending e with a new empty environment
    layer, for later knot-tying by recFix
*)
let newRec() = Rec(ref emptyBindings)

let topLayer = function (l::_) -> l | _ -> assert false

(*  
    recFix layer bs "ties the knot" 
*)
let recFix: layer -> bindings -> layer = fun layer bs -> match layer with
| Rec r  -> (r:=bs; layer) 
| _      -> failwith "recFix at invalid env"

(* Continuation Composition *)

let (>>) f g x = g(f x)


let debugMatch = ref false


(* Pattern matching generates a bindings extension *)

exception NoMatch 
let noMatch () = raise NoMatch

let loop2: ('state->'a->'b->'state) ->  'state -> ('a list * 'b list) -> 'state  = fun f ->
    let rec loop state = function ([], []) -> state | (x::xs, y::ys) -> loop (f state x y) (xs, ys) | _ -> noMatch()
    in  loop

let rec matchPat: pat -> value -> bindings -> bindings = fun p v bs -> 
if !debugMatch then eprintf "match %a with %a\n%!" pp_pat p pp_value v;
match p, v with 
| At(_, p),     v                              -> matchPat p v bs  (* just in case we left a location in *)
| Bra(p),       v                              -> matchPat p v bs  
| Id i,          _                             -> addBinding i v bs
| Tuple ps,     Tup vs'                        -> loop2 (fun bs' p v -> matchPat p v bs') emptyBindings (ps, vs')
| Con c,        Const c' when c=c'             -> emptyBindings
| Cid t,        Const(Tag t') when t=t'        -> emptyBindings
| Construct (c, ps), Cons (c', vs') when c=c'  -> loop2 (fun bs' p v -> matchPat p v bs') emptyBindings (ps, vs')
(* This is for when we don't desugar infixes *)
| Apply(pl, Cid c, pr), Cons (c', vs') when c=c' -> loop2 (fun bs' p v -> matchPat p v bs') emptyBindings ([pl;pr], vs')
(*********************************************)
(* Non-matching *)
| Construct (c, _), Cons (c', _)               -> if !debugMatch then eprintf "-- Constructors %a -- %a\n%!" pp_full_tag c pp_full_tag c'; noMatch()                                           
| _,        _                                  -> if !debugMatch then eprintf "@." else (); noMatch()
 

(* Utilities that throw errors that will eventually be detected by a type checker *)

let isTrue: value -> bool = 
    function Const(Tag(_, "True")) -> true | Const(Tag(_, "False")) -> false |   other -> semanticError @@  (Format.sprintf "Type error in guard: %s" (show_value other))

let checkArity: int -> tag -> unit = 
    fun arity -> function ((required, s)) -> if arity < required then () else semanticError @@  (Format.sprintf "Arity error applying %s [arity %d]" s required)


(* Evaluation *)

type loc = Utils.location option

   
let rec eval: loc -> env -> cont -> expr -> value = fun loc -> fun env k -> function
| Id i              -> lookup loc i k env
| Cid t             -> k(Const(Tag t))
| Con c             -> k(Const c)
| Label(name, body) -> eval loc (bind name (Prim k) env) k body
| Tuple exs         -> evalTuple loc env (fun vs -> k(Tup(List.rev vs))) [] exs
| Construct(t, exs) -> evalTuple loc env (fun vs -> k(Cons(t, List.rev vs))) [] exs 
| Bra ex            -> eval loc env k ex         
| Fn defs           -> k(Fun(env, defs))
| LazyFn case       -> k(LazyFun(env, case))
| If (g, e1, e2) ->
     let choose = fun v -> eval loc env k (if isTrue v then e1 else e2)
     in  eval loc env choose g
|    Ap (rator, rand) ->
        let rec apply = function
            | Cons(t, v)         ->  checkArity (List.length v) t; eval loc env (fun w -> k(Cons(t, v@[w]))) rand 
            | Const(Tag t)       ->  checkArity 0 t;               eval loc env (fun v -> k(Cons(t, [v]))) rand 
            | Prim f             ->  eval loc env (f >> k) rand
            | Fun(defenv, cases) ->  eval loc env (fun v -> evalCases defenv k v cases) rand
            | LazyFun(defenv, (Id i, body)) ->  
               let env' = bind i (Thunk(env, rand, ref None)) defenv 
               in  eval loc env' k body
            | (Thunk _) as op    ->  force apply op 
            | other              ->  k(Fail (show_value other))
        in  
            eval loc env apply rator
|    Apply (l, op, r) ->
        (* Runtime desugaring: for convenience in diagnostics *)
        eval loc env k (Ap(Ap(op, l), r)) 
|    Let (defs, body) -> 
         let ext  = recBindings  env defs in
         let env' = ext <+> env in
             eval loc env' k body
|    At(location, ex) ->    
       eval (Some(location)) env k ex         
              
(* |    other -> failwith (show_expr other) *)

(* Evaluates in L-R order, but the order of the result is reversed.
   This preserves linear space and time (via the continuation architecture)
*)
and evalTuple: loc -> env -> (values -> value) ->  values -> exprs -> value = fun loc e k vs -> function
| []       -> k vs
| ex::exs  -> eval loc e (fun v -> evalTuple loc e k (v::vs) exs) ex 

and recBindings : env -> defs -> layer = fun env defs ->
    let new'     = newRec() in 
    let env'     = new'<+>env in
    let rec extend bindings = function
    | [] -> bindings
    | (pat, expr) :: defs -> let v = eval None env' (fun v -> v) expr in extend (matchPat pat v  bindings) defs  
    in recFix new' @@ extend [] defs

and evalCases: env -> cont -> value -> cases -> value = fun e k v cases -> 
   let rec evalFirst: cases -> value  = function
   |   c::cs         -> (try evalCase e k v c with  NoMatch -> evalFirst cs)
   |   []            -> k(Fail (sprintf "Ran out of cases: %s" (show_value v)))
in evalFirst cases

and evalCase: env -> cont -> value -> def -> value = fun e k v -> function (lhs, rhs) -> 
    let bindings = matchPat lhs v emptyBindings in eval None (addBindings bindings e) k rhs 
    
and force k = function
|  Thunk(env, expr, vr) ->
   (match !vr with
   | None   -> eval None env (fun v -> vr:=Some v; k v) expr 
   | Some v -> k v
   ) 
|  v -> k v


let rec deepForce v = match v with
| Thunk _       -> deepForce(force (fun v->v) v)
| Tup vs        -> Tup(List.map deepForce vs)
| Cons(c, vs)   -> Cons(c, List.map deepForce vs)
| _             -> v

 












