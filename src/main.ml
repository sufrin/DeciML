open Expr
open Value
open Stdlib.Format

let num2num f = Prim (function 
    | (Const (Num n))  -> Const(Num (f n)) 
    | other            -> Fail (show_value other))

let num2bool f = Prim (function 
    | (Const (Num n))  -> Const(Bool (f n)) 
    | other            -> Fail (show_value other))
   
let num2num2num f = Prim (function 
    | (Const (Num n)) -> num2num (fun m -> f n m)
    | other           -> Fail (show_value other))

let num2num2bool f = Prim (function 
    | (Const (Num n)) -> num2bool (fun m -> f n m)
    | other           -> Fail (show_value other))

let con2bool f = Prim (function 
    | (Const n)  -> Const(Bool (f n)) 
    | other      -> Fail (show_value other))
    
let con2con2bool f = Prim (function 
    | (Const n) -> con2bool (fun m -> f n m)
    | other      -> Fail (show_value other))
    
let print = Prim 
 (fun v -> (eprintf "=========\n%s\n==========\n@." (show_value v); 
            v))
            
let id x  = x
    
let () = begin
    let prims = 
    [ ("succ",  num2num (fun n->n+1))
    ; ("pred",  num2num (fun n->n-1)) 
    ; ("print", print)
    ; ("+",     num2num2num  (fun n m -> n+m)) 
    ; ("-",     num2num2num  (fun n m -> n-m)) 
    ; ("=",     num2num2bool (fun n m -> n==m)) 
    ]
    in
    let bs = 
    [ ("x", Const(Num 24))
    ; ("y", Const(Num 25))
    ; ("z", Const(Num 26))
    ] @ prims
    in
    let env = [Bind bs]
    in 
    
    let test sx : unit = eprintf "* DeciML:\n %a ==>\n%a\n@." 
                  pp_expr  sx 
                  pp_value (eval env id sx)
    in
    let toString sx  = show_value @@ eval env id sx in
    let pr e   = Ap(Id "print", e) in 
    let tup es = Expr.Tuple es in
    let pair (x,y) = tup [x;y] in
    let iph g e1 e2 = If(g, e1, e2) in
    let lam bv body = Fn [(bv, body)] in
    let n v = Con(Num v) in
    let prt s e = pr(pair(Con(String s), e)) in
    let x    = Id "x" in 
    let y    = Id "y" in 
    let z    = Id "z" in 
    let def ds body = Let(ds, body) in
    let succ = Id "succ" in
    let add  = Id "+" in 
    let ap f x = Ap(f, x) in
    let app f x y = Ap(Ap(f, x), y) in
    let sx   = ap (ap add x) (ap succ y) in
    let sx'  = app add x y in
    let st   = pair(pr x, pr y) in
    let sw   = pr st in
    let vnil = Con(Tag (1, "nil")) in
    let (==>) x xs = Ap(Con(Tag(2, "cons")), Tuple [x;xs]) in
    (* let test sx = (eprintf "=%s@." (show_value(eval env id sx))) in *)
    (*
    test sx;
    test sx';
    test sw;
    test (ap (ap (Id "=") (n 0)) (n 0));
    test (iph (ap (ap (Id "=") (n 0)) (n 0)) (n 7)(pr(n 8)));
    test (iph (ap (ap (Id "=") (n 0)) (n 1)) (pr(n 7))(n 8));
    test (prt "x" x);
    test (prt "tuple" (tup [y;x;y;x]));
    *)
    test (x ==> y ==>  x ==> vnil);
    test (lam  (tup [x;y]) (tup [y;x;y;x]));
    test (ap (lam  (x) (tup [x;x])) (tup [n 1; n 2]));
    test (ap (lam  (tup [x;y;z]) (tup [y;x;y;x])) (tup [n 1; n 2]));
    test (ap (lam  (tup [x;y]) (tup [y;x;y;x])) (tup [x; y]));
    test (ap (lam x x) (tup [y; x]));
    test (ap (lam (tup[x;y]) x) (tup [y; x]));
    test (ap (lam (n 10) (n 12)) (n 10));
    test (ap (lam (n 10) (n 12)) (n 14));
    test (ap (lam x (ap (lam y (ap (ap add y) z)) x)) (n 17));
    test (def [(x, y); (y, z); (z, ap succ z)] (tup [x;y;z]));
    test (def [(x, y); (y, z); (z, ap succ z)] (lam z (tup [x;y;z])));
    ()
end



