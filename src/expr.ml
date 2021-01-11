open Utils

type tag  = int * string [@printer fun fmt (_,s) -> fprintf fmt "`%s" s]
            [@@deriving show { with_path = false }]

type id   = string       [@printer fun fmt s -> fprintf fmt "%s" s]
            [@@deriving show { with_path = false }]

type con  = Num    of int         [@printer fun fmt n -> fprintf fmt "%s" (string_of_int n)]
          | String of string      [@printer fun fmt s -> fprintf fmt "%s" s]
          | Bool   of bool        [@printer fun fmt b -> fprintf fmt "%s" (string_of_bool b)]
          | Tag    of tag         [@printer fun fmt t -> fprintf fmt "%s" (show_tag t)]
          [@@deriving show { with_path = false }]

type expr = Id    of id           [@printer fun fmt i  -> fprintf fmt "%s" (show_id i)]      
          | Tuple of exprs        [@printer fun fmt es -> fprintf fmt "@[(%a)@]" pp_exprs es]
          (* Retain parenthesis structure for ease of prettyprinting *)
          | Bra   of expr         [@printer fun fmt e -> fprintf fmt "(%a)" pp_expr e]
          | Con   of con          [@printer pp_con]
          | If    of expr*expr*expr
          | Ap    of expr*expr    [@printer fun fmt (f,e) -> fprintf fmt "%s %s" (show_expr f)(show_expr e)]
          (* Apply is for  convenience in generating diagnostic messages: it is desugared at runtime *)
          | Apply of expr*expr*expr 
                                  [@printer fun fmt (l,op,r) -> fprintf fmt "%a %a %a" pp_expr l pp_expr op pp_expr r]
          (***********************)
          | Fn    of cases        (* a multi-case function abstraction *)
                                  [@printer fun fmt cs -> fprintf fmt "(| %a |)" pp_cases cs]
          | Label of id   * expr  (* id names the continuation, in scope e *)  
                                  [@printer fun fmt (l,b) -> fprintf fmt "%a: %a" pp_id l pp_expr b]      
          | Let   of defs * expr  [@printer fun fmt  (defs, body) -> fprintf fmt "@[let @[%a@]@ in @[%a@]" pp_defs defs pp_expr body]
          | At    of Utils.location * expr   [@printer fun fmt  (loc, body)  -> fprintf fmt "%a %a" pp_location loc pp_expr body]
          [@@deriving show { with_path = false }]
          
and exprs = expr list [@printer pp_punct_list ", " pp_expr] 
            [@@deriving show { with_path = false }]
            
and def  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "@[%a = %a@]" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }]

and defs = def list [@printer pp_punct_list "; " pp_def]
           [@@deriving show { with_path = false }]

and case  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "@[%a -> %a@]" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }]
           
and cases = case list  [@printer pp_punct_list " | " pp_case]
            [@@deriving show { with_path = false }]

and pat  = expr        
           [@@deriving show { with_path = false }]
           
type phrase =
     | Defs of defs [@printer fun fmt defs -> fprintf fmt "@[let @[<hov 4>%a@]@];;" pp_defs defs]
     | Expr of expr [@printer fun fmt expr -> fprintf fmt "@[%a@];" pp_expr expr]
     | EndFile 
     | Nothing 
     [@@deriving show { with_path = false }]


(* Not all expressions are patterns *)                
let rec isPat: expr->bool = function
| Id    _  -> true
| Tuple ts -> List.for_all isPat ts
| Con   _  -> true
| _        -> false


type t   = expr [@printer pp_expr]
           [@@deriving show { with_path = false }]

(* For desugaring *)
let flip = Id "flip"


