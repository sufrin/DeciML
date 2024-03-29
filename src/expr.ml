open Utils

type tag  = int * string [@printer fun fmt (_,s) -> fprintf fmt "%s" s]
            [@@deriving show { with_path = false }]

let getArity: tag -> int = function (arity, _) -> arity

let pp_full_tag fmt (arity, name) =  Format.fprintf fmt "%s [arity %d]" name arity
            
type id   = string       [@printer fun fmt s -> fprintf fmt "%s" s]
            [@@deriving show { with_path = false }]

type con  = Num    of int         [@printer fun fmt n -> fprintf fmt "%s" (string_of_int n)]
          | String of string      [@printer fun fmt s -> fprintf fmt "%s" s]
          | Bool   of bool        [@printer fun fmt b -> fprintf fmt "%s" (if b then "True" else "False")]
          | Tag    of tag         [@printer fun fmt t -> fprintf fmt "%s" (show_tag t)]
          [@@deriving show { with_path = false }]

type expr = Id    of id           [@printer fun fmt i  -> fprintf fmt "%s" (show_id i)] 
          | Cid   of tag          [@printer pp_tag]
          | Con   of con          [@printer pp_con]
          | Tuple of exprs        [@printer fun fmt es -> fprintf fmt "@[(%a)@]" pp_exprs es]
          (* Retain parenthesis structure for ease of prettyprinting *)
          | Bra   of expr         [@printer fun fmt e -> fprintf fmt "(%a)" pp_expr e]
          | Construct of tag * exprs [@printer let getTag = function 
                                               | Construct(tag,_) -> Some tag
                                               | _                -> None
                                          in pp_cons getTag pp_expr]
          (* [@printer fun fmt (t,es) -> fprintf fmt "@[(%a %a)@]" pp_tag t (pp_punct_list " " pp_expr) es] *)
          | If    of expr*expr*expr [@printer fun fmt (g, e1, e2) -> 
                                           fprintf fmt "@[if %a @,@[@[then %a @]@,@[else %a@]@]@]" pp_expr g pp_expr e1 pp_expr e2]
          | Ap    of expr*expr    [@printer fun fmt (f,e) -> fprintf fmt "%s %s" (show_expr f)(show_expr e)]
          (* Apply is for  convenience in generating diagnostic messages: it is desugared at runtime *)
          | Apply of expr*expr*expr 
                                  [@printer fun fmt (l,op,r) -> fprintf fmt "%a %a %a" pp_expr l pp_expr op pp_expr r]
          | Inside of expr * expr
          | With   of expr * expr
          (***********************)
          | Record   of defs      [@printer fun fmt  defs -> fprintf fmt "@[{ @[%a@]@ }@]" pp_defs defs]
          | Select   of expr * id [@printer fun fmt (e,l) -> fprintf fmt "%a . %a" pp_expr e pp_id l ]
          (***********************)
          | Fn    of cases        (* a multi-case function abstraction *)
                                  [@printer fun fmt cs -> fprintf fmt "@[⟨ %a ⟩@]" pp_cases cs]
          | LazyFn of case        (* a lazy function abstraction *)
                                  [@printer fun fmt c -> fprintf fmt {|λλ %a|} pp_case c]
          | ByNameFn of case      (* a call-by-name function abstraction *)
                                  [@printer fun fmt c -> fprintf fmt {|λλλ %a|} pp_case c]
          | Label of id * expr  (* id names the continuation, in scope e *)  
                                  [@printer fun fmt (l,b) -> fprintf fmt "%a: %a" pp_id l pp_expr b] 
          | AndThen of (expr*expr)  [@printer fun fmt (e1, e2) -> fprintf fmt "%a >> %a" pp_expr e1 pp_expr e2] 
          | Loop  of expr         [@printer fun fmt e -> fprintf fmt "loop %a" pp_expr e]
          | Let   of defs * expr  [@printer fun fmt  (defs, body) -> fprintf fmt "@[let @[%a@]@ in @[%a@]" pp_defs defs pp_expr body]
          | At    of Utils.location * expr   [@printer fun fmt  (loc, body)  -> fprintf fmt "%a %a" pp_location loc pp_expr body]
          [@@deriving show { with_path = false }]
          
and exprs = expr list [@printer pp_punct_list ", " pp_expr] 
            [@@deriving show { with_path = false }]
            
and def  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "@[%a = %a@]" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }]

and defs = def list [@printer pp_punct_list "; " pp_def]
           [@@deriving show { with_path = false }]

and case  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "@[%a -> @[<hv>%a@]@]" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }]
           
and cases = case list  [@printer fun fmt cases -> fprintf fmt "@[<hv>%a@]" (pp_punct_list "|" pp_case) cases]
            [@@deriving show { with_path = false }]

and pat  = expr        
           [@@deriving show { with_path = false }]
           
type notation = string * int option * string list 
           [@@deriving show { with_path = false }]
           
type phrase =
     | Defs     of defs * defs          [@printer fun fmt (defs, defs') -> fprintf fmt "@[let @[%a@]\nwhere@[%a@]@];;" pp_defs defs pp_defs defs']
     | Expr     of expr                 [@printer fun fmt expr -> fprintf fmt "@[%a@];" pp_expr expr]
     | Notation of notation list        [@printer fun fmt notns -> fprintf fmt "notation %a" (pp_punct_list "; " pp_notation) notns]
     | EndFile 
     | Nothing
     | Import   of string list
     [@@deriving show { with_path = false }]



type t   = expr [@printer pp_expr]
           [@@deriving show { with_path = false }]
           

(* Expressions used in desugaring *)

open Unique
let negateOp  = Id (intern  "-")
let negateFun = Id (intern  "prim_neg")
let prim_flip = Id (intern  "`prim_flip`")






