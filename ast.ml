type 'a loc = {
    elt : 'a
  ; loc : Range.t
}

let no_loc x = {elt=x; loc=Range.norange}

type id =  string loc (* Identifiers *)

(* Types *)
type _typ =  
  | TBool 
  | TInt 
  | TRef of ref 
and typ = _typ loc

(* References *)
and _ref =  
  | RString 
  | RArray of typ 
and ref = _ref loc

type rtyp = typ option
type ftyp = typ list * rtyp

type _const =
  | CNull
  | CBool of bool
  | CInt  of int64
  | CStr  of string
  | CArr  of const list
and const = _const loc

type unop =
  | Neg      (* arithmetic negation *)
  | Lognot   (* boolean negation *)
  | Bitnot   (* bitwise negation *)

type binop =
  | Add | Sub | Mul
  | Eq | Neq | Lt | Lte | Gt | Gte
  | And | Or | IAnd | IOr
  | Shl | Shr | Sar

(* paths -------------------------------------------------------------------- *)

(*  A path identifies a value derived from a declared variable or function:

    A reference to variable x as in the expression
       x + 1
    is represented either as:
        global, [Field(x)]    -- if x is declared globally
    or 
        local, [Field(x)]     -- if x is declared locally
  
    If x is an array (possibly multidimensional), then it can be indexed:
       x[3]
    is represented as:
       global, [Field("x"); Index(Const(3))]   
      

    If f is a function, then the invocation f(3) is represented as:
       global, [Call("f", [Const(3)])]
    
    NOTE: For this project, functions are always global.  (In later 
      projects, we will also have methods, which have different scope.)

    It is possible to have paths of length greater than 1, either 
    due to multidimensional arrays:
       x[3][4]

       local, [Field("x"); Index(Const(3)); Index(Const(4))]

    or functions that return arrays:
      f(3)[4]

      global, [Call("f", [Const(3)]); Index(Const(4))]
*)

type _accessor =
  | Field of id
  | Index of exp
  | Call of id * exp list
and accessor = _accessor loc

and path = accessor list

and _exp =  
  | Const of const 
  | Path of path 
  | NewArr of typ * exp * id * exp 
  | Bop of binop * exp * exp 
  | Uop of unop * exp 
and exp = _exp loc

type _stmt =
  | Assn of path * exp 
  | Decl of decl
  | Ret of exp option
  | SCall of path
  | If of exp * block * block  
  | For of decl list * exp option * stmt option * block  
  | While of exp * block
and stmt = _stmt loc

(*
  variable declaration:
    vinit = []      (no initializer, allowed only for non reference and ? types)
    vinit = [exp]   either a singleton array or single value, depending on vty
    vinit = [exp1 .. expN]   must be an array
*)
and _decl = {ty : typ; id : id; init : exp;}
and decl = _decl loc

and block = stmt list

type args = (typ * id) list

type _fdecl = {
  rtyp : rtyp
; name : id
; args : args
; body : block        
}
and fdecl = _fdecl loc

type gdecl =
  | Gvdecl of decl    (* global variable declarations *)
  | Gfdecl of fdecl   (* global function declarations *)

type prog = gdecl list
