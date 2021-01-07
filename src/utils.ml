open Format

let rec showList punct show  = 
function   []     -> ""
|          [v]    -> show v
|          v::vs  -> sprintf "%s%s%s" (show v) punct (showList punct show vs)

let loop f = 
    let rec loop state = function [] -> state | x::xs -> loop (f state x) xs 
    in  loop

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

