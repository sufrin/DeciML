let idSet: (string, string) Hashtbl.t = Hashtbl.create 150 

let intern: string -> string = fun s -> 
    try Hashtbl.find idSet s with Not_found -> (Hashtbl.add idSet s s; s)
    
