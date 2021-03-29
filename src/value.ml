open Format
open Expr
open Utils

let shortenEnv e = if !Utils.showClosureEnv then e else []

type value  = 
 | Ref     of value ref         [@printer fun fmt v       -> fprintf fmt "ref %a" pp_value !v]
 | Const   of con               [@printer fun fmt c       -> fprintf fmt "%a" pp_con c]
 | Tup     of values            [@printer fun fmt vs      -> fprintf fmt "@[(%a)@]" (pp_punct_list "," pp_value) vs]
 | Obj     of frame             [@printer fun fmt frame   -> fprintf fmt "@[{ @[%a@] }@]"  pp_frame frame ]
 | Cons    of tag * values      [@printer let getTag = function 
                                          | Cons(tag,_) -> Some tag
                                          | _           -> None
                                          in pp_cons getTag pp_value]
 | Fun     of env * cases       [@printer fun fmt (e, cs) -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt {|@[<v>@[λ(%a)@]@;«@[<hov>%a@]@]»|} pp_cases cs pp_env (shortenEnv e) 
                                          else fprintf fmt {|@[λ(%a)@]|}  pp_cases cs
                                ] 
 | UnitFun of env * expr        [@printer fun fmt (e, body) -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt   {|@[λ()→%a@]@;«@[<hov>%a@]»|} pp_expr body pp_env (shortenEnv e) 
                                          else fprintf fmt   {|@[λ()→%a@]|} pp_expr body
                                ]
 | LazyFun of env * case        [@printer fun fmt (e, c)  -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt {|@[<v>@[λλ %a@]@;«@[<v>%a@]»@]@]|}  pp_case c pp_env (shortenEnv e) 
                                          else fprintf fmt {|@[λλ %a@]|}  pp_case c
                                ] 
 | Delay   of delayed           [@printer pp_delayed]
 | ByNameFun of env * case      [@printer fun fmt (e, c)  -> 
                                          if !Utils.showClosureEnv 
                                          then fprintf fmt {|@[<v>@[ν %a@]@;«@[<v>%a@]»@]@]|}  pp_case c pp_env (shortenEnv e) 
                                          else fprintf fmt {|@[ν %a@]|}  pp_case c
                                ] 
 | Thunk   of env * expr        [@printer fun fmt (_, e) -> fprintf fmt {|⌈%a⌉|} pp_expr e]
 | Prim    of (value -> value)  [@opaque]
 | Cont    of (value -> value)  [@opaque]
 | Strict  of (value -> value)  [@opaque]
 [@@deriving show { with_path = false }]

and 
  cont = value -> value        [@opaque]
  [@@deriving show { with_path = false }]
  
and delayed = env * expr * value option ref 
            [@printer fun fmt (env, expr, v)  -> fprintf fmt "%a%a" 
                                                             (Utils.pp_delayed pp_expr pp_value) (expr, !v)
                                                             pp_env (shortenEnv env) 
            ]
  [@@deriving show { with_path = false }]

and 
  values = value list [@printer pp_punct_list "," pp_value]
  [@@deriving show { with_path = false }]

(* Environments *)

and env = frame list [@printer fun fmt ls ->
                        let nonempty = function
                        | Rec bs -> !bs!=[]
                        | _      -> true
                        in
                        fprintf fmt "%a" (pp_punct_list "⊕" pp_frame) (List.filter nonempty ls)]
 [@@deriving show { with_path = false }]

(* TODO: this is where to add a call marker if we ever decide to support
   tail call optimization. Right now tail calls, except those that bind no
   arguments,  cause the environment to grow unnecessarily. Additional complexity
   in implementing TCO flows from the currying of binary functions.
*)
and frame = 
  | Lib      of bindings        [@printer fun fmt _ -> fprintf fmt "<library>"]
  | Bind     of bindings        [@printer pp_bindings]
  | Rec      of bindings ref    [@printer  fun fmt bs -> 
                                           let nrbs = !bs in
                                               bs := [];        (* break the cycle *)
                                               if nrbs!=[] then fprintf fmt {|%a|} pp_bindings nrbs;
                                               bs := nrbs]
  [@@deriving show { with_path = false }]

and bindings = binding list [@printer fun fmt bs -> fprintf fmt "@[<hov>%a@]" (pp_punct_list ";" pp_binding) bs]
    [@@deriving show { with_path = false }]
  
and binding = (id * value) [@printer fun fmt (i, v) -> fprintf fmt "@[%a=%a@]" pp_id i pp_value v]
    [@@deriving show { with_path = false }]
            
let lookup: location option -> id -> cont -> env -> value = fun loc i k e ->
    let rec lookupInFrames = function 
        | []    -> semanticError @@ 
                   (Format.sprintf "Unbound variable: %s %s" i (match loc with 
                                                               | None   -> "" 
                                                               | Some l -> Utils.show_location l))
        | l::ls -> match lookupInFrame l with 
                   | Some v -> k v 
                   | None   -> lookupInFrames ls
                   
        and lookupInFrame = function
        |  Rec  bs -> lookupInBindings !bs
        |  Bind bs -> lookupInBindings bs
        |  Lib bs  -> lookupInBindings bs
        
        and lookupInBindings = function 
        |  []                  -> None
        |  (n, v)::_ when n==i -> Some v                (* all ids are interned: this is fast *)
        |  _ :: bs'            -> lookupInBindings bs'
    in  lookupInFrames e

(* Used only in record comparisons *)
let directLookup: id -> frame -> value = fun name env ->
    let rec lookupInFrame = function
        |  Rec  bs -> lookupInBindings !bs
        |  Bind bs -> lookupInBindings bs
        |  Lib bs  -> lookupInBindings bs
        
        and lookupInBindings = function 
        |  []                     -> failwith name
        |  (n, v)::_ when n==name -> v                (* all ids are interned: this is fast *)
        |  _ :: bs'               -> lookupInBindings bs'
    in  lookupInFrame env
    
(* Pattern matching generates a bindings extension *)

exception NoMatch 
let noMatch () = raise NoMatch

let loop2: ('state->'a->'b->'state) ->  'state -> ('a list * 'b list) -> 'state  = fun f ->
    let rec loop state = function ([], []) -> state | (x::xs, y::ys) -> loop (f state x y) (xs, ys) | _ -> noMatch()
    in  loop
    
let (<+>)  frame env   = frame :: env

let rec binds name = function 
    | []                              -> false
    | (name', _) :: _ when name=name' -> true
    | _          :: bs                -> binds name bs

let override = fun bs bs' ->
                List.fold_right (fun ((name, _) as binding) bs -> if binds name bs then bs else binding::bs) bs' bs

let (<++>) = function Rec bs -> 
                 function Rec bs' -> 
                    Rec(ref(override !bs !bs')) (* rec with rec' *)
   
let bind: id -> value -> env -> env = fun i v e -> Bind [(i, v)]::e

let addBindings: bindings -> env -> env = fun bs e -> Bind bs :: e

let addLib: bindings -> env -> env = fun bs e -> Lib bs :: e

let addBinding: id -> value -> bindings -> bindings = fun i v bs -> if i="_" then bs else (i,v)::bs

let emptyEnv: env = []

let emptyBindings: bindings = []

(*    Recursive Environment construction  *)

(* 
    An environment built by extending e with a new empty environment
    frame, for later knot-tying by recFix
*)
let newRec() = Rec(ref emptyBindings)

(*  
    recFix frame bs "ties the knot" 
*)
let recFix: frame -> bindings -> frame = fun frame bs -> match frame with
| Rec r  -> (r:=bs; frame) 
| _      -> failwith "recFix at invalid env"


(* Continuation Composition *)

let (>>) f g x = g(f x)


let debugMatch = ref false



let rec matchPat: pat -> value -> bindings -> bindings = fun p v bs -> 
(* if !debugMatch then eprintf "match %a with %a\n%!" pp_pat p pp_value v; let b' = *)
match p, v with 
         | At(_, p),     v                              -> (matchPat ) p v bs  (* just in case we left a location in *)
         | Bra(p),       v                              -> (matchPat ) p v bs  
         | Id i,          _                             -> addBinding i v bs
         | Tuple ps,     Tup vs'                        -> loop2 (fun bs' p v -> matchPat p v bs') bs (ps, vs')
         (* | Record defs,  Obj(Rec bindings)              -> matchRecord defs !bindings bs *)
         | Con c,        Const c' when c==c'            -> bs
         | Cid t,        Const(Tag t') when t=t'        -> bs
         | Construct (c, ps), Cons (c', vs') when c==c'  -> loop2 (fun bs' p v -> matchPat p v bs') bs (ps, vs')
         (* This is for when we don't desugar infixes *)
         | Apply(pl, Cid c, pr), Cons (c', vs') when c=c' -> loop2 (fun bs' p v -> matchPat p v bs') bs ([pl;pr], vs')
         (*********************************************)
         (* Non-matching *)
         | Construct (c, _), Cons (c', _)               -> (* if !debugMatch then eprintf "-- Constructors %a -- %a\n%!" pp_full_tag c pp_full_tag c'; *) noMatch()                                           
         | _,        _                                  -> (* if !debugMatch then eprintf "@." else (); *) noMatch()
(* in if !debugMatch then eprintf "match %a with %a = %a\n%!" pp_pat p pp_value v pp_bindings b'; b' *)

    

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

let pp_loc fmt = function 
| None          -> ()
| Some location -> pp_location fmt location

let unitValue = Tup[]
let trueValue = Const(Tag(0, "True"))

  
let rec eval: loc -> env -> cont -> expr -> value = fun loc -> fun env k -> function
| Id i              -> lookup loc i k env       
| Cid t             -> k(Const(Tag t))          
| Con c             -> k(Const c)               

| Label(name, body) -> eval loc (bind name (Cont k) env) k body   (* reify and bind the continuation *)
  
| Tuple []          -> k unitValue (* Optimisation *)
| Tuple exs         -> evalTuple loc env (fun vs -> k(Tup(List.rev vs))) [] exs
| Construct(t, exs) -> evalTuple loc env (fun vs -> k(Cons(t, List.rev vs))) [] exs 
| Bra ex            -> eval loc env k ex    
| Fn[(Tuple[],rhs)] -> k (UnitFun(env, rhs)) (* Optimisation of a ()-> function *)
| Fn cases          -> k(Fun(env, cases))
| LazyFn   case     -> k(LazyFun(env, case))
| ByNameFn case     -> k(ByNameFun(env, case))
| If (g, e1, e2)    -> eval loc env (fun v -> eval loc env k (if isTrue v then e1 else e2)) g
| Ap (rator, rand)  -> eval loc env (applyTo loc env k rand) rator
| Apply (l, op, r)  -> eval loc env k (Ap(Ap(op, l), r)) (* Runtime desugaring: for convenience in diagnostics *)
| AndThen (e1, e2)  -> eval loc env (fun _ -> eval loc env k e2) e1

(* Loop is a natural delimiter for continuations *)
| Loop e            -> let rec loop = fun b -> if isTrue b then eval loc env loop e else k unitValue
                       in  loop (trueValue)

| Let (defs, body)  -> let ext  = recBindings env defs in  
                       let env' = ext <+> env in eval loc env' k body 

| Inside(e, body)   -> let frame' = evalToRecord loc env e in eval loc (frame' <+> env) k body

                                  
| With(e1, e2)      -> let frame1 = evalToRecord loc env  e1 in
                       let frame2 = evalToRecord loc env  e2 in k(Obj(frame2 <++> frame1)) 

| Select (e, i)     -> let frame = evalToRecord loc env e in k (try directLookup  i frame with _ -> semanticError @@  (Format.asprintf "No such field in selection .%s from %a at %a" i pp_frame frame pp_loc loc))

| Record defs       -> let ext  = recBindings env defs in k (Obj ext)
                                                                     
| At(location, ex)  -> eval (Some(location)) env k ex 

and evalToRecord: loc -> env -> expr -> frame = fun loc env e -> 
    let v = eval loc env (force id) e
    in  match v with 
        | Obj frame -> frame
        | other -> semanticError @@  (Format.asprintf "Type error (record expected) %a at %a" pp_value other pp_loc loc)
              
and applyTo: loc -> env -> cont -> expr -> value -> value = fun loc env k rand -> function
| Cons(t, v)            ->  checkArity (List.length v) t; 
                            eval loc env (fun w -> k(Cons(t, v@[w]))) rand 
| Const(Tag t)          ->  checkArity 0 t;               
                            eval loc env (fun v -> k(Cons(t, [v]))) rand 

(*  *)
| Cont f                ->  eval loc env           f  rand    
| Prim f                ->  eval loc env (      f>>k) rand
| Strict f              ->  eval loc env (force f>>k) rand

(* Stack Optimisation: I think ocaml simplifies the continuation construction because it ignores its argument *)
| UnitFun(defenv, body) -> eval loc env (fun _ -> eval loc defenv k body) rand  

| Fun(defenv, cases)    -> eval loc env (fun v -> evalCases loc defenv k v cases) rand

| LazyFun(defenv, (Id i, body)) ->  
   let env' = bind i (match rand with 
                     | Con c -> Const c 
                     | _     -> Delay(env, rand, ref None)) defenv                      
   in  eval loc env' k body
   
| ByNameFun(defenv, (Id i, body)) ->  
   let env' = bind i (match rand with 
                     | Con c -> Const c 
                     | _     -> Thunk(env, rand)) defenv                                          
   in  eval loc env' k body
   
| (Delay _) as op    ->  force (applyTo loc env k rand) op 
| (Thunk _) as op    ->  force (applyTo loc env k rand) op 
| other              ->  semanticError @@ (asprintf "applying non-function value: %a %s" pp_value other (match loc with None -> "" | Some l -> Utils.show_location l))


(* 
   Evaluates in L-R order, but the order of the result is reversed.
   This preserves linear space and time (via the continuation
   architecture).  It would be more elegant and efficient to keep
   the ast expr list in reverse order in the first place. But most
   tuples are little. (* TODO *)
*)
and evalTuple: loc -> env -> (values -> value) ->  values -> exprs -> value = fun loc e k vs -> function
| []       -> k vs
| ex::exs  -> eval loc e (fun v -> evalTuple loc e k (v::vs) exs) ex 

and recBindings: env -> defs -> frame = fun env defs ->
    (* closures made during defs elaboration all embody new',  an empty Rec frame *)
    let new'     = newRec()   in 
    let env'     = new'<+>env in
    (* augment bindings frame as specified by defs *)
    let rec elaborate : bindings -> defs -> bindings = fun bindings -> function 
    | [] -> bindings
    | (pat, expr) :: defs -> 
       let v = eval None env' (fun v -> v) expr in elaborate (matchPat pat v bindings) defs
    in (* elaborate the definitions and tie the knot *)
       recFix new' @@ elaborate [] defs

(* Find the first case whose lhs pattern matches the value, then evaluate its rhs *)
and evalCases: loc -> env -> cont -> value -> cases -> value = fun loc e k v cases -> 
   let rec evalFirst: cases -> value  = function
   |   c::cs         -> (try evalCase e k v c with  NoMatch -> evalFirst cs)
   |   []            -> semanticError @@  (asprintf "No case matches: %s in application at %a" (show_value v) pp_loc loc)
in evalFirst cases

and evalCase: env -> cont -> value -> def -> value = fun e k v -> function (lhs, rhs) -> 
    let bindings = matchPat lhs v emptyBindings in eval None (addBindings bindings e) k rhs 
    
and force k = function
|  Delay(env, expr, vr) ->
   (match !vr with
   | None   -> eval None env (fun v -> vr:=Some v; k v) expr 
   | Some v -> k v
   ) 
|  Thunk (env, expr) -> eval None env k expr
|  v -> k v

(* Strict structural equality predicate *)    
and val_eq: value -> value -> bool = fun l r -> match force id l, force id r with 
| Const k1,  Const  k2  -> k1=k2 
| Tup   vs1, Tup    vs2 -> 
  if List.length vs1 = List.length vs2 then
     List.fold_left2  (fun ok l r -> if ok && val_eq l r then ok else false) true vs1 vs2
  else false
| Cons (t1, vs1), Cons (t2, vs2) -> 
  if t1=t2 && List.length vs1 = List.length vs2 then
     List.fold_left2  (fun ok l r -> if ok && val_eq l r then ok else false) true vs1 vs2
  else false
| Obj env1, Obj env2 -> frameEq env1 env2 
| _, _ -> false


(* Environment relations: for records *)
and frameEq frame1 frame2 = 
    let forallPairs frame p  =
        let rec forFrame    = function Rec bs -> forBindings !bs | Bind bs | Lib bs -> forBindings bs
            and forBindings = function [] -> true | b::bs -> p b && forBindings bs
        in  forFrame frame
    in let subEnv l r = try forallPairs l (fun (name, v) -> val_eq v (directLookup name r)) with _ -> false
    in frame1==frame2 || subEnv frame1 frame2 && subEnv frame2 frame1



let rec deepForce v = match v with
| Delay (_,_,rv)   -> (match !rv with None -> deepForce(force (fun v->v) v) | Some v -> v)
| Tup vs           -> Tup(List.map deepForce vs)
| Cons(c, vs)      -> Cons(c, List.map deepForce vs)
| _                -> v

 






















