(*
        Parser for DeciML expressions
*)

%{

        let mkNum(base, first, buf) = Expr.Con(Expr.Num(Utils.num_value base first buf))
        
        let mkString s = Expr.Con(Expr.String s)
        
        let mkId s = Expr.Id s
        
        let mkTuple = function
            | [x] -> Expr.Bra x
            | xs  -> Expr.Tuple xs
            
        let mkFun cases = Expr.Fn cases

%}

%token <int*int*string> NUM (* base, start, rep *)

%token <string> ID CONID EQ 
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
                CONS
                
%token <string*string*string> LEFT RIGHT
                
%token <string> STRING (* a string encoded in utf8 *)
                
%token <string> CHAR   (* a string encoded in utf8 *)

%token FUN NUF LAM CURLYBRA CURLYKET BRA KET COMMA DOT  AT TO LET REC AND WHERE IN
       END ALL COLON SEMI EOF IF THEN ELSE SQBRA SQKET
       DATA ALT IMPORT HOLE 
       NOTATION TYPE INSIDE DEF WITH DO
       ENDEXPR

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
%right BINR3, CONR3
%left  BINL3, CONL3
%right BINR4, CONR4, CONS
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
        |       CONS                            {$1}

%inline 
SECTFIX : INFIX {$1}
        | EQ    {$1}

let phrase := 
    | LET; ~=defs; END; <Expr.Defs>
    | ~=expr; ENDEXPR;          <Expr.Expr>
    | SEMI;             {Expr.Defs []}
    | ENDEXPR;          {Expr.Defs []}
    | EOF;              {Expr.EndFile}

let defs     == ~=revdefs;              <List.rev>
let cases    == ~=revcases;             <List.rev>
let exprlist == ~=revexprlist;          <List.rev>
      
let revdefs := 
    | ~=def;                   {[def]}
    | ~=revdefs; eol; ~=def;  {def::revdefs}
    
let eol == SEMI; ENDEXPR | ENDEXPR
let eoc == ENDEXPR? ; ALT
    
let def :=
    | ~=id; EQ; ~=expr;     { (id, expr) }

let revcases := 
    | ~=case;                    {[case]}
    | ~=revcases; eoc; ~=case;  { case::revcases }
    
let case :=
    | ~=id; TO; ~=expr;      { (id, expr) }
    
let expr := 
    | ~=term;                                   <>
    | LET; ~=defs; IN; ~=expr;                  <Let>
    | IF; g=expr; THEN; e1=expr; ELSE; e2=expr; { If(g, e1, e2)}
    | t1=term; op=INFIX; t2=expr;               {Ap(Ap(Id op, t1), t2)}

let term :=
    | ~=app; <>    

let app :=
    | ~=prim;                           <>
    | ~=app; ~=prim;                    <Ap>
    
    
let prim :=
    | ~=id;                              <>
    | ~=NUM;                             <mkNum>
    | ~=STRING;                          <mkString>
    | BRA; ~=exprlist; KET;              <mkTuple>
    | LAM; BRA; eoc?; ~=cases; KET;      <mkFun>
    | FUN; ~=cases; ENDEXPR?; NUF;       <mkFun>


let revexprlist :=
    |                               { []}
    | ~=expr;                       { [expr]}
    | ~=revexprlist; COMMA; ~=expr; { expr::revexprlist }

id  : 
    |  name=ID                      { mkId name }

