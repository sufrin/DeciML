open Sedlexing

type token = ExprParser.token

open ExprParser

(*****************************  Symbol Table *************************) 
    let to_string: int -> string = fun u ->
    let b = Buffer.create 4
    in  Buffer.add_utf_8_uchar b @@ Uchar.of_int u;
        Buffer.contents b
 
 
    let idMap: (string, token)       Hashtbl.t  = Hashtbl.create 150 
    
    let notation mkTok codes = 
        let addCode code =
            let str = to_string code
            in Hashtbl.add idMap str (mkTok str)
        in List.iter addCode codes
    
    let _ = List.iter (fun (s, t) -> Hashtbl.add idMap s t)
       [       "let"      , LET
       ;       "in"       , IN
       ;       "end"      , END
       ;       "if"       , IF
       ;       "then"     , THEN
       ;       "else"     , ELSE
       ;       "import"   , IMPORT
       ;       "notation" , NOTATION
       ]

(* Syntactic roles of identifier strings are looked up by the scanner using mkXXXX 
   All identifiers that appear are mapped by the idMap to their default or declared role
*)
    
    let ret id sym = (Hashtbl.add idMap id sym; sym)
    
    let mkID      id = try Hashtbl.find idMap id with Not_found -> ret id @@ ID id
    let mkCONID   id = try Hashtbl.find idMap id with Not_found -> ret id @@ CONID id
    let mkMath    id = try Hashtbl.find idMap id with Not_found -> ret id @@ BINL9 id
    let mkMathCon id = try Hashtbl.find idMap id with Not_found -> ret id @@ CONL9 id

       
    let leftOpSymbol = Array.of_list
    [ (fun x -> BINL0(x))
    ; (fun x -> BINL1(x))
    ; (fun x -> BINL2(x))
    ; (fun x -> BINL3(x))
    ; (fun x -> BINL4(x))
    ; (fun x -> BINL5(x))
    ; (fun x -> BINL6(x))
    ; (fun x -> BINL7(x))
    ; (fun x -> BINL8(x))
    ; (fun x -> BINL9(x))
    ]
    
    let rightOpSymbol = Array.of_list
    [ (fun x -> BINR0(x))
    ; (fun x -> BINR1(x))
    ; (fun x -> BINR2(x))
    ; (fun x -> BINR3(x))
    ; (fun x -> BINR4(x))
    ; (fun x -> BINR5(x))
    ; (fun x -> BINR6(x))
    ; (fun x -> BINR7(x))
    ; (fun x -> BINR8(x))
    ; (fun x -> BINR9(x))
    ]
 
    let leftConSymbol = Array.of_list
    [ (fun x -> CONL0(x))
    ; (fun x -> CONL1(x))
    ; (fun x -> CONL2(x))
    ; (fun x -> CONL3(x))
    ; (fun x -> CONL4(x))
    ; (fun x -> CONL5(x))
    ; (fun x -> CONL6(x))
    ; (fun x -> CONL7(x))
    ; (fun x -> CONL8(x))
    ; (fun x -> CONL9(x))
    ]
    
    let rightConSymbol = Array.of_list
    [ (fun x -> CONR0(x))
    ; (fun x -> CONR1(x))
    ; (fun x -> CONR2(x))
    ; (fun x -> CONR3(x))
    ; (fun x -> CONR4(x))
    ; (fun x -> CONR5(x))
    ; (fun x -> CONR6(x))
    ; (fun x -> CONR7(x))
    ; (fun x -> CONR8(x))
    ; (fun x -> CONR9(x))
    ]

   (* Experimental notation declarations *)
    
    let showNotation = ref false   
 
    let declareNotations declns =
        let declareFixity (associativity, priority, symbols) =
            let priority = match priority with Some p->p | None -> 9 in
            if (0<=priority && priority<=9) then
               let mkTok = match associativity with
                  "left"      -> leftOpSymbol.(priority)
                | "right"     -> rightOpSymbol.(priority)
                | "leftdata"  -> leftConSymbol.(priority)
                | "rightdata" -> rightConSymbol.(priority)
                | "id"        -> (fun x -> ID x)
                | "constant"  -> (fun x -> CONID x)
                | _           -> failwith ("fixity misdeclared as: "^associativity^", but should be one of: left, right, leftdata, rightdata, id, con) ")
               in 
               let addSymbol str = Hashtbl.add idMap str (mkTok str);
                                   if !showNotation then Format.fprintf Format.std_formatter "notation %s %d %s\n%!" associativity priority str
               in 
                  List.iter addSymbol symbols           
            else failwith ("priority out of bounds: " ^ string_of_int priority)
    in List.iter declareFixity declns
    
    
    let mkOP =
    function
    |  "->"   -> TO 
    |  "\\"   -> LAM    
    |  "\\\\" -> LAZY    
    |  s      ->  mkMath s

(******************************************************)       

exception LexError of Lexing.position * string

let blank         = [%sedlex.regexp? ' ' | '\t']

let newline       = [%sedlex.regexp? '\r' | '\n' ]

let whitespace    = [%sedlex.regexp? Plus (blank | newline)]

let decimal_ascii = [%sedlex.regexp? Plus ('0' .. '9')]

let octal_ascii   = [%sedlex.regexp? "0o", Plus ('0' .. '7')]

let hex_ascii     = [%sedlex.regexp? "0x", Plus (('0' .. '9' | 'a' .. 'f' | 'A' .. 'F'))]

let alpha         = [%sedlex.regexp?  ('a' .. 'z' | 'A' .. 'Z' | '_') ] 
let greek         = [%sedlex.regexp?  (0x0391 .. 0x03ff) ]  
let digit         = [%sedlex.regexp?  ('0' .. '9') ] 
let ident         = [%sedlex.regexp?  ('a' .. 'z'), Star(alpha|digit) ]
let cident        = [%sedlex.regexp?  ('A' .. 'Z'), Star(alpha|digit) ]

let stringChunk   = [%sedlex.regexp? Star (Compl ('"' | '\\' | '\n'))]

let mathop        = [%sedlex.regexp? (0x27f0 .. 0x27ff | 0x2900 .. 0x297x |
                                      0x2200 .. 0x22ff | 0x2190 .. 0x21ff |
                                      0x2a00 .. 0x2aff | 0x2300 .. 0x23ff)]

let aop           = [%sedlex.regexp? Chars ":+-=#&*/~\\!@<>?|" | 0x00d7 (* × *)]


let rec skipWhitespace buf =
  match%sedlex buf with
  | Plus whitespace -> skipWhitespace buf
  | _               -> ()

let string buf  =
  let buffer = Buffer.create 10 in
  let rec read_string buf  =
    match%sedlex buf with
    | eof                 -> err "End of file in string" buf
    | '\n'                -> err "End of line in string" buf
    | "\\\""              -> ins "\"" buf
    | "\\\\"              -> ins "\\" buf
    
    | "\\n"               -> ins "\n" buf
    | "\\\n", Star blank, "\\"  -> read_string buf
    | "\\\n", Star blank, stringChunk  -> ins (Utf8.lexeme buf) buf (* err "Wrong continuation line after \\ at line end in string" buf *)
    
    | '"'                 -> Buffer.contents buffer
    | stringChunk         -> ins (Utf8.lexeme buf) buf
    | _                   -> assert false
    and err s buf = raise @@ LexError (fst @@ lexing_positions buf,  s)
    and ins s buf = Buffer.add_string buffer s; read_string buf
  in
    read_string buf
    
let comment echo buf =
    match%sedlex buf with
    | Star(Compl newline), newline -> if echo then Format.fprintf Format.std_formatter "--+%s%!" (Utf8.lexeme buf) else ()
    | _                            -> assert false
     
let rec token buf =
  match%sedlex buf with
  | eof -> EOF
  | "--+"       -> comment true  buf; token buf
  | "---"       -> comment false buf; token buf
  | ';'         -> SEMI
  | ";;"        -> END
  | newline     -> token buf
  | blank       -> token buf
  | 0x27e8      -> FUN  (* ⟨ *)
  | 0x27e9      -> NUF  (* ⟩⟩ *)
  (*
  | "{"         -> CBRA
  | "}"         -> CKET
  *)
  | '|'         -> ALT
  | 0x03bb      -> LAM  (* λ *)                             
  | 0x2192      -> TO   (* → *)
  | '"'         -> STRING(string buf)
  | ','         -> COMMA
  | '='         -> EQ           (Utf8.lexeme buf)
  | '('         -> BRA
  | ')'         -> KET
  | ident       -> mkID         (Utf8.lexeme buf)
  | cident      -> mkCONID      (Utf8.lexeme buf)
  | greek       -> mkID         (Utf8.lexeme buf)
  | mathop      -> mkMath       (Utf8.lexeme buf)
  | aop, Star aop -> mkOP       (Utf8.lexeme buf)
  | decimal_ascii -> NUM(10, 0, Utf8.lexeme buf) 
  | octal_ascii   -> NUM(8,  2, Utf8.lexeme buf) 
  | hex_ascii     -> NUM(16, 2, Utf8.lexeme buf) 
  | _ ->
    let pos  = fst @@ lexing_positions buf in
    let _    = Sedlexing.next buf in (* Skip the bad character: pretend it's a token *)
    let tok  = Utf8.lexeme buf in  
    raise @@ LexError (pos,  "Unexpected character: "^tok)

let lexer buf =
  Sedlexing.with_tokenizer token buf








