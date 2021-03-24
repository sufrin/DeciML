(*
        Parser for DeciML expressions
        
*)

%{
        
        open Expr
        open Utils
        
        

        let mkNum(base, first, buf) = Con(Num(Utils.num_value base first buf))
        
        let mkPriority(base, first, buf) = Utils.num_value base first buf
        
        let mkString s = Con(String s)
        
        (* Remove topmost bracket or location information *)
        let rec rawExpr = function
        | At(_, e) -> rawExpr e
        | Bra e    -> rawExpr e
        | e        -> e
        
        let mkId          s = Id s
        let mkConId tag = Cid tag
        
        let mkExpr = function 
         | CONL0 s | CONL1 s | CONL2 s | CONL3 s | CONL4 s | CONL5 s | CONL6 s | CONL7 s | CONL8 s | CONL9 s 
         | CONR0 s | CONR1 s | CONR2 s | CONR3 s | CONR4 s | CONR5 s | CONR6 s | CONR7 s | CONR8 s | CONR9 s -> Cid(2, s)
         | BINL0 s | BINL1 s | BINL2 s | BINL3 s | BINL4 s | BINL5 s | BINL6 s | BINL7 s | BINL8 s | BINL9 s 
         | BINR0 s | BINR1 s | BINR2 s | BINR3 s | BINR4 s | BINR5 s | BINR6 s | BINR7 s | BINR8 s | BINR9 s -> Id s
         | CONID tag -> Cid tag
         | ID    s   -> Id s
         | _         -> failwith "Expression uses notation from unsound notation declaration"

                
        (* Transform unsaturated applications of proper constructors into Constructs. *)
        
        let rec  mkAp loc (rator, rand) = 
        match rator with
        |  Bra rator -> mkAp loc (rator, rand)
        |  Cid tag ->     
               if getArity tag==0 then 
               let res = Ap(rator, rand) in begin 
                  syntaxWarning @@ Format.asprintf "Constant used in construction %a %a" pp_expr res pp_location loc;
                  res 
               end else
                  Construct(tag, [rand])
         | Construct(tag, exs) ->
               let res = Construct(tag, exs@[rand]) in
               let arity = getArity tag in
               if arity <= List.length exs then 
                  syntaxWarning @@ Format.asprintf "Constructor of arity %d used in construction %a %a" arity pp_expr res pp_location loc;
               res
        | _ -> if !idLocs then At(loc, Ap(rator, rand)) else Ap(rator, rand)
        
        (* Expose the name of an operator -- for notation declarations *)
        let rec opToString = function
            | Id s           -> s
            | Cid(_,s)       -> s
            | At(_, op)      -> opToString op
            | _              -> assert false
            
        (* Distinguish proper tuples from bracketed expressions *)
        (* We keep the bracket in the ast to simplifiy prettyprinting during diagnostivs *)    
        let mkTuple = function
            | [x] -> Bra x
            | xs  -> Tuple xs
            
        let mkFun cases = Fn cases
        
        
        let rec mkLambda(bvs, body) = 
        match bvs with 
        | [pat]     -> Fn[(rawExpr pat, body)]
        | pat::pats -> Fn[(rawExpr pat, mkLambda(pats, body))]
        | []        -> Fn[(Tuple[], body)]
           
        
        let rec mkLazy(bvs, body) = 
            match bvs with 
            | [pat]     -> LazyFn(rawExpr pat, body)
            | pat::pats -> LazyFn(rawExpr pat, mkLazy(pats, body))
            | _         -> assert false
        
        let rec mkByName(bvs, body) = 
            match bvs with 
            | [pat]     -> ByNameFn(rawExpr pat, body)
            | pat::pats -> ByNameFn(rawExpr pat, mkByName(pats, body))
            | _         -> assert false
                
        let mkBind loc (id, bvs, body) = 
            let lambda = mkLazy(bvs, body) in mkAp loc (id, lambda)
        
        let mkDef loc (pattern, body) = 
            let rec abstractFrom expr pat = 
            (* Format.eprintf "Abstractfrom (%a) %a\n%!" pp_expr expr pp_expr pat; *)
            let pat = rawExpr pat in
            match pat with
            | Id    _
            | Con   _
            | Cid   _
            | Construct   _
            | Tuple _           -> (pat, expr)
            | Apply(el, op, er) -> abstractFrom expr (mkAp loc (mkAp loc (op, el), er))
            | Ap(rator, rand) ->
            ( let rand = rawExpr rand in
              match rand with
              | Id _
              | Con   _
              | Cid   _
              | Construct   _
              | Apply _ 
              | Tuple _ -> abstractFrom (Fn [(rand, expr)]) rator
              | _       -> syntaxError (Format.asprintf "Erroneous operand %a within lhs of definition at %a\n%!" pp_expr rand pp_location loc) 
            )
            | _  -> syntaxError (Format.asprintf "Erroneous pattern %a within lhs of definition at %a\n%!" pp_expr pat pp_location loc)
         in abstractFrom body pattern
                  
         let quoteLeftfix loc (id, right, _, _, isData) (right') =
             if   right=right' 
             then Bra(if isData then Cid(2, id) else Id id)
             else syntaxError (Format.asprintf "opening %s should be closed by %s (not %s) at %a\n%!" id right right' pp_location loc)
          
         let quoteOutfix loc (id, right, empty, cons, isData) right' =
             if right=right' 
             then Bra(if isData then Cid(1, id) else Id id)
             else syntaxError (Format.asprintf "opening %s should be closed by %s (not %s) at %a\n%!" id right right' pp_location loc)

         let mkOutfixList loc (id, right, empty, cons, isData) exprs (right') =  
         try
             let  cons  = mkExpr cons  in
             let  empty = mkExpr empty in
             let  foldexprs exprs = List.fold_right (fun e r -> Ap (Ap (cons, e), r)) exprs empty     in     
             if   right=right' 
             then Ap(Bra(if isData then Cid(1, id) else Id id), foldexprs exprs) 
             else syntaxError (Format.asprintf "opening %s should be closed by %s (not %s) at %a\n%!" id right right' pp_location loc)
         with 
             Failure msg -> syntaxError (Format.asprintf "outfix %s ... %s at %a (%s)\n%!" id right pp_location loc msg)
         
         let mkOutfix loc (id, right, empty, cons, isData) expr (right') =
             if   right=right' 
             then Ap(Bra(if isData then Cid(1, id) else Id id), expr) 
             else syntaxError (Format.asprintf "opening %s should be closed by %s (not %s) at %a\n%!" id right right' pp_location loc)

         let mkQuant loc (id, right, _, _, isData) expr right' body =
             if   right=right' 
             then Ap(Ap(Bra(if isData then Cid(2, id) else Id id), expr), body)
             else syntaxError (Format.asprintf "quantifier %s should be followed %s (not %s) at %a\n%!" id right right' pp_location loc)
             
%}

%token <int*int*string> NUM (* base, start, rep *)

(* we associate arity with constant symbols to support runtime sanity checking *)
%token <int*string>  
       CONID 
       
%token <string> 
        PREFIX
        ID 
        EQ 
        BINR0 BINL0 CONR0 CONL0
        BINR1 BINL1 CONR1 CONL1
        BINR2 BINL2 CONR2 CONL2
        BINR3 BINL3 CONR3 CONL3
        BINR4 BINL4 CONR4 CONL4
        BINR5 BINL5 CONR5 CONL5
        BINR6 BINL6 CONR6 CONL6
        BINR7 BINL7 CONR7 CONL7
        BINR8 BINL8 CONR8 CONL8
        BINR9 BINL9 CONR9 CONL9
                
%token <string*string*token*token*bool> LEFT LEFTFIX LISTLEFT (* the boolean controls whether it's a data symbol or an id *)

%token <string> RIGHT LEFTMID BIND 
 
                
%token <string> STRING (* a string encoded in utf8 *)
                

%token FUN ALT NUF LAM LAZY BYNAME BRA KET CBRA CKET SBRA SKET COMMA TO LET IN
       END SEMI EOF IF THEN ELSE DOT
       NOTATION IMPORT LABEL DEF WHERE ANDTHEN LOOP





(* Infix symbols *)

%right BINR0, CONR0
%left  BINL0, CONL0
%right BINR1, CONR1 
%left  BINL1, CONL1
%right BINR2, CONR2
%left  BINL2, CONL2
%right BINR3, CONR3, EQ
%left  BINL3, CONL3
%right BINR4, CONR4
%left  BINL4, CONL4
%right BINR5, CONR5
%left  BINL5, CONL5
%right BINR6, CONR6
%left  BINL6, CONL6
%right BINR7, CONR7
%left  BINL7, CONL7
%right BINR8, CONR8
%left  BINL8, CONL8
%right BINR9, CONR9
%left  BINL9, CONL9

(**************************************************************************)
%type <int option> priority

%start          phrase 
%type           <Expr.phrase> phrase
%%


(*******************ALL THIS INLINING IS NECESSARY TO AVOID S/R CONFLICTS ********)

%inline
BINR    :  BINR0 {$1} | BINR1 {$1} | BINR2 {$1} | BINR3 {$1} | BINR4 {$1} 
        |  BINR5 {$1} | BINR6 {$1} | BINR7 {$1} | BINR8 {$1} | BINR9 {$1}
%inline
BINL    :  BINL0 {$1} | BINL1 {$1} | BINL2 {$1} | BINL3 {$1} | BINL4 {$1} 
        |  BINL5 {$1} | BINL6 {$1} | BINL7 {$1} | BINL8 {$1} | BINL9 {$1}
%inline
CONR    :  CONR0 {$1} | CONR1 {$1} | CONR2 {$1} | CONR3 {$1} | CONR4 {$1} 
        |  CONR5 {$1} | CONR6 {$1} | CONR7 {$1} | CONR8 {$1} | CONR9 {$1}
%inline
CONL    :  CONL0 {$1} | CONL1 {$1} | CONL2 {$1} | CONL3 {$1} | CONL4 {$1} 
        |  CONL5 {$1} | CONL6 {$1} | CONL7 {$1} | CONL8 {$1} | CONL9 {$1}

let infix   ==  ~=BINL;                 < mkId >
            |   ~=BINR;                 < mkId >
            |   op=CONL;                { mkConId(2, op) }
            |   op=CONR;                { mkConId(2, op) }

let infixop ==  ~=infix;                <>
            |   ~=EQ;                   < mkId >
                
(********************************************************************************)

let phrase := 
    | LET; ~=defs; ~=where; endoreof;                   < Expr.Defs >
    | ~=topexpr;   terminator;                          < Expr.Expr >
    | NOTATION; ~=notations; endoreof;                  < Expr.Notation >
    | IMPORT; paths=spec+ ; terminator;                 < Expr.Import >
    | SEMI;                                             { Expr.Nothing }
    | END;                                              { Expr.Nothing }
    | EOF;                                              { Expr.EndFile }
    
let where == WHERE; ~=defs;                             { defs }
          |                                             { [] }
          
let spec  == path=STRING;                               { path } 
          |  path=ID;                                   { path }

let endoreof   == END      | EOF
let terminator == endoreof | SEMI

let defs     ==
    |                                                   { [] }
    |  ~=revdefs;                                       <List.rev>

let cases    == 
    |                                                   { [] }
    | ~=revcases;                                       < List.rev >
    
let exprlist == 
    |                                                   { [] }
    | ~=revexprlist;                                    < List.rev >


let notations :=
    | ~=notation;                                       { [notation] }
    | ~=notation; SEMI; ~=notations;                    { notation :: notations }
    
let notation := 
    | lr=ID; bp=priority; ~=symbols;                    { (lr, bp, symbols) } 
    
let priority == value=NUM;                              { Some(mkPriority value)} 
             |                                          { None }
    
let symbols := 
    | { [] }
    | op=infix;    ~=symbols;                           { opToString op :: symbols }
    | op=id;       ~=symbols;                           { opToString op :: symbols }
    | op=prefixop; ~=symbols;                           { opToString op :: symbols }
    | op=xfix;     ~=symbols;                           { op :: symbols }
    
let xfix := op=LEFT;                                    { let (id, _, _, _, _) = op in id }
    |       op=LEFTFIX;                                 { let (id, _, _, _, _) = op in id }
    |       op=LISTLEFT;                                { let (id, _, _, _, _) = op in id }
    |       op=LEFTMID;                                 <>
    |       op=RIGHT;                                   <>
      
let revdefs := 
    | ~=def;                                            { [def] }
    | ~=revdefs; eod; ~=def;                            { def::revdefs }
    
let eod == SEMI
let eoc == ALT
    
let def :=
    | lhs=lhsexpr; EQ; body=topexpr;                     { mkDef $loc (lhs, body) }

let revcases := 
    | ~=case;                                            {[case]}
    | ~=revcases; eoc; ~=case;                           { case::revcases }
    
let case :=
    | ~=expr; TO; ~=topexpr;                             { (expr, topexpr) }

let topexpr :=
    | LET; ~=defs; IN; ~=topexpr;                        { Let(defs, topexpr) }
    | IF; g=topexpr; THEN; e1=topexpr; ELSE; e2=topexpr; { If(g, e1, e2) }
    | LAZY; bvs=bid+; TO; body=topexpr;                  < mkLazy >
    | BYNAME; bvs=bid+; TO; body=topexpr;                < mkByName >
    | LAM;  bvs=bid+; TO; body=topexpr;                  < mkLambda >
    | LAM; BRA; KET;  TO; body=topexpr;                  { mkLambda([], body) }
    | ~=bindop;  bvs=bid+; TO; body=topexpr;             { mkBind $loc (bindop, bvs, body) }
    | q=LEFTFIX;  ~=expr; m=LEFTMID; body=topexpr;            { mkQuant $loc q expr m body }
    | el=expr; ANDTHEN; er=topexpr;                      { AndThen(el, er) }
    | label=ID; LABEL; ~=topexpr;                        < Label > 
    | LOOP; ~=topexpr;                                   < Loop > 
    | ~=expr;                                            <>
    
let expr := 
    | ~=term;                                            { term }
    | el=expr; op=infixop; er=expr;                      { if !Utils.desugarInfix then 
                                                              mkAp $loc (mkAp $loc (op, el), er) 
                                                           else 
                                                             Apply(el, op, er)
                                                         }
let lhsexpr := 
    | ~=term;                                            { term }
    | el=lhsexpr; op=infix; er=lhsexpr;                  { if !Utils.desugarInfix then 
                                                             mkAp $loc (mkAp $loc (op, el), er)
                                                           else 
                                                             Apply(el, op, er) 
                                                         }
let term :=
    | ~=app;                                             <> 

let app :=
    | ~=prim;                                            { prim }
    | ~=app; ~=prim;                                     { mkAp $loc (app,prim) }
    
    
let prim :=
    | ~=simplex;                                         { simplex }
    
    (* Sections *)
    | BRA; op=infixop; ~=expr; KET;                      {if op=negateOp then 
                                                             Bra(mkAp $loc (negateFun, expr)) 
                                                          else 
                                                             Bra(mkAp $loc (mkAp $loc (prim_flip, Bra(op)), expr))
                                                         }   
    | BRA; ~=expr; op=infixop; KET;                      { Bra(mkAp $loc (Bra(op), expr)) }
    
    (* Balanced *)
    | BRA; eoc; ~=cases; eoc; KET;                       { mkFun cases }
    | FUN; eoc?; ~=cases; NUF;                           { mkFun cases }
    

let simplex := 
    | ~=id;                                               { id }
    | ~=NUM;                                              < mkNum >
    | ~=STRING;                                           < mkString >
    | ~=prefixop; ~=simplex;                              { mkAp $loc (prefixop,simplex) }  
    | BRA; ~=exprlist; KET;                               < mkTuple >
    | openb=LISTLEFT; ~=exprlist; closeb=RIGHT;           { mkOutfixList $loc openb exprlist closeb }
    | openb=LEFT;     ~=expr;     closeb=RIGHT;           { mkOutfix $loc openb (expr) closeb }
    (* quotation of infixes, leftfixes, outfixes, etc *)
    | BRA; openb=LISTLEFT; DOT; closeb=RIGHT;        KET; { quoteOutfix  $loc openb closeb }  (* Special case of quotation *)
    | BRA; openb=LEFT;     DOT; closeb=RIGHT;        KET; { quoteOutfix  $loc openb closeb }  (* Special case of quotation*)
    | BRA; openb=LEFTFIX;  DOT; closeb=LEFTMID; DOT; KET; { quoteLeftfix $loc openb closeb }  (* Special case of quotation*)
    | BRA; op=infixop;  KET;                              { Expr.Bra(op) }
    | BRA; op=prefixop; KET;                              { Expr.Bra(op) }
    | BRA; op=bindop;   KET;                              { Expr.Bra(op) }
    
let revexprlist :=
    | expr=topexpr;                                      { [expr]}
    | ~=revexprlist; COMMA; expr=topexpr;                { expr::revexprlist }

id  : 
    |  name=ID                                           { if !idLocs then At($loc, mkId name) else mkId name }
    |  name=CONID                                        { mkConId name }

bid  : 
     |  name=ID                                          { if !idLocs then At($loc, mkId name) else mkId name }

prefixop : 
     |  name=PREFIX                                      { if !idLocs then At($loc, mkId name) else mkId name }

bindop : 
     |  name=BIND                                        { if !idLocs then At($loc, mkId name) else mkId name }


















