open Format

let rec showList punct show  = 
function   []     -> ""
|          [v]    -> show v
|          v::vs  -> sprintf "%s%s%s" (show v) punct (showList punct show vs)

let loop f = 
    let rec loop state = function [] -> state | x::xs -> loop (f state x) xs 
    in  loop
    
(* Positions and locations *)

let pp_pos  out { Ppxlib.pos_lnum; pos_cnum; pos_bol; _} = 
    Format.fprintf out "%d:%d"  pos_lnum (pos_cnum - pos_bol)

let pp_fpos out { Ppxlib.pos_lnum; pos_cnum; pos_bol; pos_fname; _} = 
    Format.fprintf out "%s %d:%d"  pos_fname pos_lnum (pos_cnum - pos_bol)

type location = Ppxlib.position * Ppxlib.position

let pp_location out loc =
    Format.fprintf out "%a-%a" pp_fpos (fst loc) pp_pos (snd loc)

let show_location loc =
    Format.asprintf "%a-%a" pp_fpos (fst loc) pp_pos (snd loc)
    
(* Numbers *)

let digit_value c =
  let open Stdlib in
  match c with
  | 'a' .. 'f' -> 10 + Char.code c - Char.code 'a'
  | 'A' .. 'F' -> 10 + Char.code c - Char.code 'A'
  | '0' .. '9' -> Char.code c - Char.code '0'
  | _ -> assert false

let num_value base first buf =
  let c = ref 0 in
      for i = first to String.length buf - 1 do
        let v = digit_value buf.[i] in
       assert (v < base);
        c := (base * !c) + v
      done;
      !c

(* Needs some hov refinement *)

let pp_punct_list punct pp_item  fmt items =
  Format.pp_open_box fmt 1;
  begin match items with
  | [] -> ()
  | hd :: tl ->
      pp_item fmt hd;
      tl |> List.iter begin fun item ->
        Format.pp_print_string fmt punct;
        Format.pp_print_space fmt ();
        pp_item fmt item
      end
  end;
  Format.pp_close_box fmt ()

(* Semantic error exceptions *)

exception SemanticError of string
let semanticError: string -> 'a = fun s -> raise (SemanticError s)

exception SyntaxError   of string
let syntaxError: string -> 'a = fun s -> raise (SyntaxError s)


let syntaxWarning s = Format.eprintf "Warning: %s\n" s

(* Switches *)

let desugarInfix = ref false

and idLocs = ref false 

and showEnv = ref false


