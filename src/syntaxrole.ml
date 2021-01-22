(*  
    The lexer provides the machinery for associating abstract
    roles with names that are used when prettyprinting expressions 
    and values. 
    
    Utils depends functionally on this module
    
    ExprLexer depends "formally" on it because it
    "exports" its getRole abstraction function 
    to this module once and for all at initialization
    time.
    
    This is the simplest way TODAY to avoid a cyclic dependency
    between Utils, ExprLexer, ExprParser. A cleaner way would
    be to have the parser and lexer and utils all depend on
    this module, and with the token type, symbol-hashtable, etc
    /all/ defined in here. This would be possible if Menhir
    supported the importing of external symbol definitions: it 
    might, but I'm not inclined to deal with detail TODAY (22/1/2021)
*)
type assoc = L | R
type role  = Infix of assoc*int | Nonfix
let  getrole: (string -> role) ref = ref (fun _ -> Nonfix)
let  setGetRole: (string -> role) -> unit = fun getter -> getrole := getter
let  getRole s = !getrole s

