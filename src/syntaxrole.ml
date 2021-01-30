(*  
    The lexer provides the machinery for associating abstract
    roles with names that are used when prettyprinting expressions 
    and values. 
    
    Utils depends functionally on this module
    
    ExprLexer depends "formally" on it because it
    "exports" its getRole abstraction function 
    to this module once and for all at initialization
    time.
    
    This is the simplest way TODAY to avoid a cyclic dependency
    between Utils, ExprLexer, ExprParser. A cleaner way would
    be to have the parser and lexer and utils all depend on
    this module, and with the token type, symbol-hashtable, etc
    /all/ defined in here. This would be possible if Menhir
    supported the importing of external symbol definitions: it 
    might, but I'm not inclined to deal with detail TODAY (22/1/2021)
*)
type assoc = L | R
type role  = Infix of assoc*int | Nonfix | Confix
let  getrole: (string -> role) ref = ref (fun _ -> Nonfix)
let  setGetRole: (string -> role) -> unit = fun getter -> getrole := getter
let  getRole s = !getrole s

let maxBP = 1024 (* MUST BE LARGER THAN 4*the largest priority *)

let getBP: string -> int = fun name ->
match getRole name with
| Infix(_, n) -> n
| _           -> maxBP

(* 
    Bracketing policy for infix constructions is somewhat conservative
    * constructions with the same constructor are bracketed if the associativity 
      direction warrants it
    * constructions with different infix constructors are always bracketed
    * constructions with lower binding power are always bracketed
*)

(* Bracket the term with tag t if it appears as the left operand *)
let bracketLeft  t (name', assoc', bp') = 
    match t with
    | None -> false
    | Some (_, name) -> 
      (name == name' && assoc'=R) || getBP name < bp' (* || name !=name' *)

(* Bracket the term with tag t if it appears as the right operand *)
let bracketRight (name, assoc, bp) t  = 
    match t with
    | None -> false
    | Some (_, name') -> 
      (name == name' && assoc=L) ||  getBP name' < bp  (* || name !=name' *)

