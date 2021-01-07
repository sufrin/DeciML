open Sexplib.Std
open Utils

type tag  = int * string [@printer fun fmt (_,s) -> fprintf fmt "`%s" s]
            [@@deriving show { with_path = false }, sexp]

type id   = string       [@printer fun fmt s -> fprintf fmt "%s" s]
            [@@deriving show { with_path = false }, sexp]

type con  = Num    of int         [@printer fun fmt n -> fprintf fmt "%s" (string_of_int n)]
          | String of string      [@printer fun fmt s -> fprintf fmt "%s" s]
          | Bool   of bool        [@printer fun fmt b -> fprintf fmt "%s" (string_of_bool b)]
          | Tag    of tag         [@printer fun fmt t -> fprintf fmt "%s" (show_tag t)]
          [@@deriving show { with_path = false }, sexp]

type expr = Id    of id           [@printer fun fmt i  -> fprintf fmt "%s" (show_id i)]      
          | Tuple of exprs        [@printer fun fmt es -> fprintf fmt "(%a)" pp_exprs es]
          | Con   of con          [@printer pp_con]
          | If    of expr*expr*expr
          | Ap    of expr*expr    [@printer fun fmt (f,e) -> fprintf fmt "(%s %s)" (show_expr f)(show_expr e)]
          | Fn    of cases        (* a multi-case function abstraction *)
                                  [@printer fun fmt cs -> fprintf fmt "{ %a }" pp_cases cs]
          | Label of id   * expr  (* id names the continuation, in scope e *)  
                                  [@printer fun fmt (l,b) -> fprintf fmt "%a: %a" pp_id l pp_expr b]      
          | Let   of defs * expr  [@printer fun fmt  (defs, body) -> fprintf fmt "let @[%a@]\nin %a" pp_defs defs pp_expr body]
          [@@deriving show { with_path = false }, sexp]
          
and exprs = expr list [@printer pp_punct_list ", " pp_expr] 
            [@@deriving show { with_path = false }, sexp]
            
and def  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "%a = %a" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }, sexp]

and defs = def list [@printer pp_punct_list "\n" pp_def]
           [@@deriving show { with_path = false }, sexp]

and case  = pat * expr  [@printer fun fmt (p, e) -> fprintf fmt "%a -> %a" pp_pat p pp_expr e]
           [@@deriving show { with_path = false }, sexp]
           
and cases = case list  [@printer pp_punct_list "| " pp_case]
            [@@deriving show { with_path = false }, sexp]

and pat  = expr         
           [@@deriving show { with_path = false }, sexp]
           


(* Not all expressions are patterns *)                
let rec isPat: expr->bool = function
| Id    _  -> true
| Tuple ts -> List.for_all isPat ts
| Con   _  -> true
| _        -> false

type t   = expr [@printer pp_expr]
           [@@deriving show { with_path = false }, sexp]




