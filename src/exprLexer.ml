open Sedlexing

type token = ExprParser.token

let braCount = ref 0 
let incBra() = incr braCount
let decBra() = decr braCount
let inBra()  = not(!braCount == 0)


open ExprParser

exception LexError of Lexing.position * string

let blank         = [%sedlex.regexp? ' ' | '\t']

let newline       = [%sedlex.regexp? '\r' | '\n' ]

let whitespace    = [%sedlex.regexp? Plus (blank | newline)]

let decimal_ascii = [%sedlex.regexp? Plus ('0' .. '9')]

let octal_ascii   = [%sedlex.regexp? "0o", Plus ('0' .. '7')]

let hex_ascii     = [%sedlex.regexp? "0x", Plus (('0' .. '9' | 'a' .. 'f' | 'A' .. 'F'))]

let alpha         = [%sedlex.regexp?  ('a' .. 'z' | 'A' .. 'Z' | '_') ] 
let digit         = [%sedlex.regexp?  ('0' .. '9') ] 
let ident         = [%sedlex.regexp?  alpha, Star(alpha|digit) ]

let stringChunk   = [%sedlex.regexp? Star (Compl ('"' | '\\' | '\n'))]


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
    | Star(Compl newline), newline -> if echo then Format.fprintf Format.std_formatter "%s%!" (Utf8.lexeme buf) else ()
    | _                            -> assert false
     
let rec token buf =
  match%sedlex buf with
  | eof -> EOF
  | "--+"  -> comment true  buf; token buf
  | "--"   -> comment false buf; token buf
  | ';'    -> SEMI
  | ";;"   -> END
  | newline -> if inBra() then token buf else ENDEXPR 
  | blank   -> token buf
  | "end"  -> END
  | "let"  -> LET
  | "in"  -> IN
  | "if"  -> IF
  | "then"  -> THEN
  | "else"  -> ELSE
  | "|"  -> ALT
  | "{"  -> FUN
  | "}"  -> NUF
  | "->"  -> TO
  | '-' -> BINL6 (Utf8.lexeme buf)
  | '+' -> BINR6 (Utf8.lexeme buf)
  | '.' -> DOT
  | '"' -> STRING(string buf)
  | ',' -> COMMA
  | '=' -> EQ (Utf8.lexeme buf)
  | '(' -> incBra(); BRA
  | ')' -> decBra(); KET
  | decimal_ascii -> NUM(10, 0, Utf8.lexeme buf) 
  | octal_ascii   -> NUM(8,  2, Utf8.lexeme buf) 
  | hex_ascii     -> NUM(16, 2, Utf8.lexeme buf) 
  | ident         -> ID (Utf8.lexeme buf)
  | _ ->
    let pos  = fst @@ lexing_positions buf in
    let _    = Sedlexing.next buf in (* Skip the bad character: pretend it's a token *)
    let tok  = Utf8.lexeme buf in  
    raise @@ LexError (pos,  "Unexpected character: "^tok)

let lexer buf =
  Sedlexing.with_tokenizer token buf





