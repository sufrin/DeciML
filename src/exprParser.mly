(*
        Parser for DeciML expressions
        
*)

%{
        
        open Expr

        let mkNum(base, first, buf) = Expr.Con(Expr.Num(Utils.num_value base first buf))
        
        let mkString s = Expr.Con(Expr.String s)
        
        let mkId    s = Expr.Id s
        let mkConId s = Con(Tag (0,s))
        
        let mkTuple = function
            | [x] -> Expr.Bra x
            | xs  -> Expr.Tuple xs
            
        let mkFun cases = Expr.Fn cases
        
        let rec mkLambda(bvs, body) = 
            match bvs with 
            | [pat]     -> Expr.Fn[(pat, body)]
            | pat::pats -> Expr.Fn[(pat, mkLambda(pats, body))]
            | _         -> assert false
        
        let rec mkLazy(bvs, body) = 
            match bvs with 
            | [pat]     -> Expr.LazyFn(pat, body)
            | pat::pats -> Expr.LazyFn(pat, mkLazy(pats, body))
            | _         -> assert false
            
        let mkDef (pattern, body) = 
            let rec abstractFrom expr pat = 
            (* Format.eprintf "Abstractfrom (%a) %a\n%!" pp_expr expr pp_expr pat; *)
            match pat with
            | Bra p          -> abstractFrom expr p
            | Id    _
            | Con   _
            | Tuple _ -> (pat, expr)
            | Apply(el, op, er) -> abstractFrom expr (Ap(Ap(op, el), er))
            | Ap(rator, ((Id _) as rand)) -> abstractFrom (Expr.Fn [(rand, expr)]) rator
            | Ap(rator, rand) ->
            ( match rand with
              | Con   _
              | Tuple _ -> abstractFrom (Expr.Fn [(rand, expr)]) rator
              | _       -> (Format.eprintf "Erroneous pattern: %a in %a%!" pp_expr pat pp_expr pattern; failwith "Syntax")
            )
            | _        -> (Format.eprintf "Erroneous pattern: %a in %a%!" pp_expr pat pp_expr pattern; failwith "Syntax")
         in abstractFrom body pattern
             

%}

%token <int*int*string> NUM (* base, start, rep *)

%token <string> 
        ID CONID EQ 
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
                
%token <string*string*string> LEFT RIGHT
                
%token <string> STRING (* a string encoded in utf8 *)
                

%token FUN ALT NUF LAM LAZY BRA KET COMMA TO LET IN
       END SEMI EOF IF THEN ELSE DOT
       NOTATION IMPORT

%right TO

(* Increasing priorities: operators 
%right        WHERE
%right        WITH
%right        AT
%left         DOT
*)

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

%start          phrase 
%type           <Expr.phrase> phrase
%%

(**************************************************************************)


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

%inline        
INFIX   :       BINL                            {$1}
        |       BINR                            {$1}
        |       CONL                            {$1}
        |       CONR                            {$1}
        |       EQ                              {$1}

let phrase := 
    | LET; ~=defs; endoreof;        <Expr.Defs>
    | ~=topexpr;   terminator;      <Expr.Expr>
    | NOTATION; notations; endoreof; 
                {(*Utils.declareNotations;*) Expr.Nothing}
    | SEMI;             {Expr.Nothing}
    | END;              {Expr.Nothing}
    | EOF;              {Expr.EndFile}

let endoreof == END | EOF
let terminator == endoreof | SEMI

let defs     == ~=revdefs;              <List.rev>
let cases    == ~=revcases;             <List.rev>
let exprlist == ~=revexprlist;          <List.rev>

let notations :=
    | ~=notation;                       {[notation]}
    | ~=notation; SEMI; ~=notations;    {notation :: notations}
    
let notation := 
    | lr=ID; bp=NUM?; ~=symbols;         { (lr, bp, symbols) }
    
let symbols := 
    | { [] }
    | op=INFIX; ~=symbols; { op::symbols }
    | op=ID;    ~=symbols; { op::symbols }
    | op=CONID; ~=symbols; { op::symbols }
      
let revdefs := 
    | ~=def;                  {[def]}
    | ~=revdefs; eod; ~=def;  {def::revdefs}
    
let eod == SEMI
let eoc == ALT
    
let def :=
    | lhs=expr; EQ; body=topexpr;     { mkDef(lhs, body) }

let revcases := 
    | ~=case;                    {[case]}
    | ~=revcases; eoc; ~=case;  { case::revcases }
    
let case :=
    | ~=expr; TO; ~=topexpr;      { (expr, topexpr) }

let topexpr :=
    | LET; ~=defs; IN; ~=topexpr;                  { Let(defs, topexpr) }
    | IF; g=expr; THEN; e1=expr; ELSE; e2=topexpr; { If(g, e1, e2)}
    | LAZY; bvs=id+; TO; body=topexpr;             <mkLazy>
    | LAM; bvs=patterns; TO; body=topexpr;         <mkLambda>
    | LAM; BRA; ~=cases; KET;                      <mkFun>
    | ~=expr; <>
    
let expr := 
    | ~=term;                                   {term}
    | t1=expr; op=INFIX; t2=expr;               {Apply(t1, Id op, t2)}

let term :=
    | ~=app; <>    

let app :=
    | ~=prim;                           {prim}
    | ~=app; ~=prim;                    {Ap(app,prim)}
    
    
let prim :=
    | ~=simplex;                         {simplex}
    (* Sections *)
    | BRA; op=INFIX; ~=expr; KET;        {Bra(Ap(Ap(Expr.flip, Bra(Id op)), expr))}   
    | BRA; ~=expr; op=INFIX; KET;        {Bra(Ap(Bra(Id op), expr))}
    (* Balanced *)
    | BRA; eoc; ~=cases; eoc; KET;       <mkFun>
    | FUN; eoc?; ~=cases; NUF;           <mkFun>

let patterns == simplex+

let simplex == 
    | ~=id;                              {id}
    | ~=NUM;                             <mkNum>
    | ~=STRING;                          <mkString>
    | BRA; ~=exprlist; KET;              <mkTuple>
    | BRA; op=INFIX; KET;                {Expr.Bra(Id op)}
    
let revexprlist :=
    |                               { []}
    | ~=expr;                       { [expr]}
    | ~=revexprlist; COMMA; ~=expr; { expr::revexprlist }

id  : 
    |  name=ID                      { mkId name }
    |  name=CONID                   { mkConId name }

