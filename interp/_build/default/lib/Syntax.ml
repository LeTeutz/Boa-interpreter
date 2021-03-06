type name = string

type arithop = Plus | Minus | Times | Divide | Remainder

type cmpop = Less | Equal | Unequal

type boolop = And | Or

type expr =
  | Var of name                      
  | Bool of bool                     
  | Int of int                       
  | ArithOp of arithop * expr * expr 
  | Not of expr                      
  | CmpOp of cmpop * expr * expr     
  | BoolOp of boolop * expr * expr   
  | If of expr * expr * expr         
  | Skip                             
  | Seq of expr * expr               
  | Let of name * expr * expr        
  | App of expr * expr               
  | Fun of name * expr               
  | This                             
  | Object of (name * expr) list     
  | Copy of expr                     
  | With of expr * expr              
  | Project of expr * name           
  | Assign of expr * name * expr     

type toplevel_cmd =
  | Expr of expr (* Expression to be evaluated *)
  | Def of name * expr (* Global definition [let x = e] *)