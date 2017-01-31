open Ll
open Ast

(* translation context ------------------------------------------------------ *)

(* Each part of the context is just a mapping from source identifiers
   (represented as strings) to their target representation.  Each map
   is just an association list.

   - the funs field keeps track of globally declared functions, their
     corresponding target gid's, and their (source) types

   - the global field keeps track of other global identifiers.  Unlike
     functions and locals, we need to know the _target_ type information 
     about globals (see the discussion about global arrays for why)

   - the local field maps source local variables to their
     corresponding target uid's and (source) types.  The frontend
     should maintain the invariant that uid' LL type corresponding to
     a local variable of Ast.typ t is Ptr(cmp_typ t).  That is, local 
     variables denote addresses in memory                                     

   Note: although the gid and uid components of a binding are just strings
   and, indeed, the frontend will always map the source identifier "x" to 
   a target gid or uid "x", we maintain the distinction here to highlight
   the fact that, conceptually, the source identifier string and the target 
   identifier string don't have to be identical -- the context maps
   one to the other.                                                          *)

type funs_binding   = (gid * Ast.ftyp)
type global_binding = (gid * Ast.typ * Ll.ty)
type local_binding  = (uid * Ast.typ)

type ctxt = {
  funs    : (string * funs_binding)   list;   (* Functions scope *)
  global  : (string * global_binding) list;   (* Global scope *)
  local   : (string * local_binding)  list;   (* Local scope  *)
}

let empty_ctxt = { funs   = []; global = []; local  = []; }

(* extending the context ---------------------------------------------------- *)

(* these add functions check to make sure that the identifier isn't already 
   bound in the context.                                                      *)
let add_function (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.funs then
    failwith @@ Printf.sprintf "Function %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with funs = (id.elt, bnd)::c.funs}

let add_global (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.global then
    failwith @@ Printf.sprintf "Global %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with global = (id.elt, bnd)::c.global}

let add_local (c:ctxt) (id:id) bnd : ctxt =
  if List.mem_assoc id.elt c.local then
    failwith @@ Printf.sprintf "Local %s already defined. %s" id.elt
      (Range.string_of_range id.loc)
  else {c with local = (id.elt,bnd)::c.local}

(* looking up a binding in the context -------------------------------------- *)

(* these functions raise the exception Not_found if there is no binding 
   for the identifier present in the context                                  *)

let lookup_function (id:string) (c:ctxt) : (uid * Ast.ftyp) =
    List.assoc id c.funs

let lookup_local (id:string) (c:ctxt) : (uid * Ast.typ) =
    List.assoc id c.local

let lookup_global (id:string) (c:ctxt) : (gid * Ast.typ * Ll.ty) =
    List.assoc id c.global
