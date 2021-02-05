open Format
open Expr
open Utils

let shortenEnv e = if !Utils.showClosureEnv then e else []

type value  = 
 | Ref     of value ref         [@printer fun fmt v       -> fprintf fmt "ref %a" pp_value !v]
 | Const   of con               [@printer fun fmt c       -> fprintf fmt "%a" pp_con c]
 | Tup     of values            [@printer fun fmt vs      -> fprintf fmt "@[(%a)@]" (pp_punct_list "," pp_value) vs]
 | Cons    of tag * values      [@printer let getTag = function 
                                          | Cons(tag,_) -> Some tag
                                          | _           -> None
                                          in pp_cons getTag pp_value]
 | Fun     of env * cases       [@printer fun fmt (e, cs) -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt {|@[<v>@[λ(%a)@]@;«@[<hov>%a@]@]»|} pp_cases cs pp_env (shortenEnv e) 
                                          else fprintf fmt {|@[λ(%a)@]|}  pp_cases cs
                                ] 
 | LazyFun of env * case        [@printer fun fmt (e, c)  -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt {|@[<v>@[λλ %a@]@;«@[<v>%a@]»@]@]|}  pp_case c pp_env (shortenEnv e) 
                                          else fprintf fmt {|@[λλ %a@]|}  pp_case c
                                ] 
 | Thunk   of thunk             [@printer pp_thunk]
 | Prim    of (value -> value)  [@opaque]
 | Cont    of (value -> value)  [@opaque]
 | Strict  of (value -> value)  [@opaque]
 | Unbound of id                [@printer fun fmt id      -> fprintf fmt "Unbound %s" (show_id id)]
 | Fail    of string            [@printer fun fmt why     -> fprintf fmt "FAIL %s" why]
 [@@deriving show { with_path = false }]

and 
  cont = value -> value        [@opaque]
  [@@deriving show { with_path = false }]
  
and thunk = env * expr * value option ref 
            [@printer fun fmt (env, expr, v)  -> fprintf fmt "@[<v>%a@;%a@]" 
                                                             (pp_th pp_expr pp_value) (expr, !v)
                                                             pp_env (shortenEnv env) 
            ]
  [@@deriving show { with_path = false }]

and 
  values = value list [@printer pp_punct_list "," pp_value]
  [@@deriving show { with_path = false }]

(* Environments *)

and env = layer list [@printer fun fmt ls ->
                        let nonempty = function
                        | Rec bs -> !bs!=[]
                        | _      -> true
                        in
                        fprintf fmt "%a" (pp_punct_list "⊕" pp_layer) (List.filter nonempty ls)]
 [@@deriving show { with_path = false }]

and layer = 
  | Lib      of bindings        [@printer fun fmt bs -> fprintf fmt "<library>"]
  | Bind     of bindings        [@printer pp_bindings]
  | Rec      of bindings ref    [@printer  fun fmt bs -> 
                                           let nrbs = !bs in
                                               bs := [];
                                               if nrbs!=[] then fprintf fmt {|%a|} pp_bindings nrbs;
                                               bs := nrbs
                                ]
  [@@deriving show { with_path = false }]

and bindings = binding list [@printer fun fmt bs -> 
                                      fprintf fmt "@[<hov>%a@]" (pp_punct_list "," pp_binding) bs
                            
                            ]
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
    
(* Pattern matching generates a bindings extension *)

exception NoMatch 
let noMatch () = raise NoMatch

let loop2: ('state->'a->'b->'state) ->  'state -> ('a list * 'b list) -> 'state  = fun f ->
    let rec loop state = function ([], []) -> state | (x::xs, y::ys) -> loop (f state x y) (xs, ys) | _ -> noMatch()
    in  loop
    
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

let isTrue: value -> bool = function 
    | Const(Tag(_, "True"))  -> true 
    | Const(Tag(_, "False")) -> false 
    | other                  -> semanticError @@  (Format.sprintf "Type error in guard: %s" (show_value other))

let checkArity: int -> tag -> unit = 
    fun arity -> function ((required, s)) -> 
        if arity < required then () else semanticError @@  (Format.sprintf "Arity error applying %s [arity %d]" s required)


(* Evaluation *)

type loc = Utils.location option

let unitValue = Tup[]
let trueValue = Const(Tag(0, "True"))
  
let rec eval: loc -> env -> cont -> expr -> value = fun loc -> fun env k -> function
| Id i              -> lookup loc i k env
| Cid t             -> k(Const(Tag t))
| Con c             -> k(Const c)
| Label(name, body) -> eval loc (bind name (Cont k) env) k body
| Tuple exs         -> evalTuple loc env (fun vs -> k(Tup(List.rev vs))) [] exs
| Construct(t, exs) -> evalTuple loc env (fun vs -> k(Cons(t, List.rev vs))) [] exs 
| Bra ex            -> eval loc env k ex     
| Fn defs           -> k(Fun(env, defs))
| LazyFn case       -> k(LazyFun(env, case))
| If (g, e1, e2)    -> eval loc env (fun v -> eval loc env k (if isTrue v then e1 else e2)) g
| Ap (rator, rand)  -> eval loc env (applyTo loc env k rand) rator
| Apply (l, op, r)  -> eval loc env k (Ap(Ap(op, l), r)) (* Runtime desugaring: for convenience in diagnostics *)
| AndThen (e1, e2)  -> eval loc env (fun _ -> eval loc env k e2) e1
| Loop e            -> let rec loop = fun b -> if isTrue b then eval loc env loop e else k unitValue
                       in  loop (trueValue)
| Let (defs, body)  -> let ext  = recBindings  env defs in let env' = ext <+> env in eval loc env' k body 
| At(location, ex)  -> eval (Some(location)) env k ex         
              
and applyTo: loc -> env -> cont -> expr -> value -> value = fun loc env k rand -> function
| Cons(t, v)         ->  checkArity (List.length v) t; eval loc env (fun w -> k(Cons(t, v@[w]))) rand 
| Const(Tag t)       ->  checkArity 0 t;               eval loc env (fun v -> k(Cons(t, [v]))) rand 
| Cont f             ->  eval loc env f rand
| Prim f             ->  eval loc env (f >> k) rand
| Strict f           ->  eval loc env (force f >> k) rand
| Fun(defenv, cases) ->  eval loc env (fun v -> evalCases defenv k v cases) rand
| LazyFun(defenv, (Id i, body)) ->  
   let env' = bind i (match rand with Con c -> Const c | _ -> Thunk(env, rand, ref None)) defenv 
   in  eval loc env' k body
| (Thunk _) as op    ->  force (applyTo loc env k rand) op 
| other              ->  k(Fail ("Applying non-function value: " ^ show_value other))


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
| Thunk (_,_,rv) -> (match !rv with None -> deepForce(force (fun v->v) v) | Some v -> v)
| Tup vs         -> Tup(List.map deepForce vs)
| Cons(c, vs)    -> Cons(c, List.map deepForce vs)
| _              -> v

 













