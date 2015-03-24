open Ll
open Ctxt
open Ast

(* Overview ----------------------------------------------------------------- *)

(* The job of the frontend is to translate the abstract syntax into
   the LLVM IR, implementing the source language semantics in terms of
   the target language constructs.

   Because the LLVM IR is typed, the frontend must also propagate
   enough type information so that we can generate appropriate type
   annotations at the LLVM level.  For Oat v.1, the type system is
   simple enough that the frontend can typecheck the abstract syntax
   during the compilation process.  The structure of the compiler
   therefore mirrors the form of the Oat source language typechecking
   rules, which are available from the project web pages.                     *)



(* Instruction Streams ------------------------------------------------------ *)

(* The compiler emits code by generating a stream of instructions interleaved
   with labels and values (like string constants) that should be hoisted to
   the global scope.  

   The result of each translation function (typically) includes a stream.     *)
type elt = 
  | L of lbl                (* Block labels *)
  | I of uid * insn         (* LL IR instruction *)
  | T of terminator         (* Block terminators *)
  | G of gid * Ll.gdecl     (* Hoisted Globals (usually strings) *)

type stream = elt list

(* This is occassionally useful for debugging.                                *)
let string_of_elt = function
  | L lbl         -> Printf.sprintf "L: %s" lbl
  | I (uid, insn) -> Printf.sprintf "I: %s = %s" uid (Ll.string_of_insn insn)
  | T t           -> Printf.sprintf "T: %s" (Ll.string_of_terminator t)
  | G (gid, g)    -> Printf.sprintf "G: %s = %s" gid (Ll.string_of_gdecl g)


(* During generation, we typically emit code so that it is in
   _reverse_ order when the stream is viewed as a list.  That is,
   instructions closer to the head of the list are to be executed
   later in the program.  That is because cons is more efficient than
   append


   To help make code generation easier, we define snoc (reverse cons)
   and reverse append, which let us write code sequences in their
   natural order.                                                             *)
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x


(* Convert an instruction stream into a control flow graph and a list
   of globals.

   - assumes that the instructions are in 'reverse' order of execution.

   - the returned global declarations are the "hoisted" string
     constants that appear in the function body

     For example, the source oat program:

     string f() { return "a fresh string"; }

     would translate to LL code that introduces a new global string
     constant (gid, (str_arr_typ, GString "a fresh string")).
     The string constant is introduced by the cmp_const function.             *)
let build_cfg (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
  let blocks_of_stream (code:stream) =
    let (gs, insns, term_opt, blks) =  List.fold_left
	(fun ((gs:(Ll.gid * Ll.gdecl) list), insns, term_opt, blks) e ->
           begin match e with
             | L l ->
               begin match term_opt with
                 | None ->
                   if (List.length insns) = 0 then  (gs, [], None, blks)
                   else failwith @@
                     Printf.sprintf "build_cfg: block labeled %s has\
                                     no terminator" l
                     
                 | Some terminator ->
                   (gs, [], None, (l, {insns; terminator})::blks)
               end
             | T t  -> (gs, [], Some t, blks)
             | I (uid,insn)  -> (gs, (uid,insn)::insns, term_opt, blks)
             | G (gid,gdecl) ->  ((gid,gdecl)::gs, insns, term_opt, blks)
           end)
        ([], [], None, []) code
    in
    begin match term_opt with
      | None -> failwith "build_cfg: entry block has no terminator" 
      | Some terminator ->
        ({insns; terminator}, blks), gs
    end
  in
    blocks_of_stream code 


(* Ast helper functions ----------------------------------------------------- *)

let ast_int = no_loc Ast.TInt
let ast_bool = no_loc Ast.TBool    
let ast_str = no_loc @@ Ast.TRef(no_loc RString)

(* make an Ast array type carrying t *)
let ast_array_typ t =
  no_loc @@ TRef(no_loc @@ RArray(t))

(* make an Ast constant int out of an OCaml int *)
let ast_int_exp i =
  no_loc @@ Const(no_loc @@ CInt(Int64.of_int i))



(* Compiling Types ---------------------------------------------------------- *)

(* Compile Oat types to LLVM types.  Arrays are represented as a
   pointer to a structure of the form {i64, [0 x t]}.  The first i64
   stores the size of the array.  A C-style string is stored as a
   pointer to an array of chars, with no length information, since Oat
   strings are immutable.

   NOTE: cmp_typ is the translation of the *expression* types of the
   language.  Thus a source expression of type t will have LL type
   (cmpt_typ t) while a source path of type t will have LL type
   Ptr(cmp_ty t) when used on the left-hand side of an assignment.            *)

let t_int  : Ll.ty = I64
let t_bool : Ll.ty = I1
let t_str  : Ll.ty = Ptr I8

let str_arr_typ s = Array(1 + String.length s, I8)

let rec cmp_typ (t:Ast.typ) =
  match t.elt with
  | Ast.TBool  -> t_bool
  | Ast.TInt   -> t_int
  | Ast.TRef r -> Ptr (cmp_ref r)

and cmp_ref (r:Ast.ref) =
  match r.elt with
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_typ u)]

let cmp_rtyp r =
  match r with
  | None -> Void
  | Some t -> cmp_typ t

let cmp_ftyp ((args,ret):Ast.ftyp) : Ll.fty = 
  (List.map cmp_typ args, cmp_rtyp ret)



(* LL IR helper functions --------------------------------------------------- *)

(* Generate a fresh identifier based on a given string.  Because Oat 
   identifiers cannot begin with _ the resulting string is guaranteed
   not to clash with another source language construct.                       *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

let sym = gensym

(* Compile Ocaml constants to LL IR constant operands of the right type.      *)
let i1_op_of_bool b   = Ll.Const (if b then 1L else 0L)
let i64_op_of_int i   = Ll.Const (Int64.of_int i)
let i64_op_of_int64 i = Ll.Const i

(* Compute a gep path to index into an Oat array represented as LL type:
    {i64, [ 0 x u] }*                                                         *)
let gep_array_index (i:operand) = [
  i64_op_of_int 0;   (* dereference the pointer *)
  i64_op_of_int 1;   (* focus on the array component of the struct *)
  i;                 (* index into the array *)
]

(* Compute a gep path to the length field of an Oat array.                    *)
let gep_array_len = [
  i64_op_of_int 0;  (* dereference the pointer *)
  i64_op_of_int 0;  (* focus on the length component of the struct *)
]

let ty_of_unop (uop:Ast.unop) : ty =
    match uop with
    | Ast.Neg _ | Ast.Bitnot _ -> (cmp_typ (Ast.no_loc Ast.TInt))
    | Ast.Lognot _ -> (cmp_typ (Ast.no_loc Ast.TBool))

(* Generate a call to the runtime.c function oat_alloc_array.  t is
   the src type size is an i64 operand, the number of elements in the
   array returns: an operand of type (cmp_ty (Ast.TArray t)) and the
   code for allocating the array.  Note that because oat_alloc_array is
   polymorphic (its proper return type is generic in the element type),
   we have to use the Bitcast operation to let LL IR know what type the
   array should have.                                                         *)

let oat_alloc_array_dynamic (t:Ast.typ) (size:operand) : operand * stream =
  let ans_id = gensym "array" in
  let ans_ty = cmp_typ @@ ast_array_typ t in
  let arr_id = gensym "raw_array" in
  let arr_ty = cmp_typ @@ ast_array_typ ast_int in
  (Id ans_id,
   [ I (arr_id, Call(arr_ty, Gid "oat_alloc_array", [(I64, size)])) ] >::
   I (ans_id, Bitcast(arr_ty, Id arr_id, ans_ty))) 

let oat_alloc_array_static (t:Ast.typ) (n:int) : operand * stream=
  oat_alloc_array_dynamic t (Ll.Const(Int64.of_int n))







 
(* Compile a constant ------------------------------------------------------- *)

(* Invariant: cn is a source constant that should be checked to have
   type source type t.  The result is the compiled type, an operand of
   that type and a stream that correctly initializes the operand. 

   Unlike global constants (handled by the cmp_init function), constant 
   arrays that appear in function bodies need to allocate fresh storage.
   Otherwise, two calls to the function f below would return the _same_
   reference, when each call should create a fresh copy of the array.

    int[] f() {
      return {1;2;3}
    }

   For CArr, your compiler should emit code that allocates a fresh array 
   and then initializes it with the constant values.

*)
let rec cmp_const  (cn:Ast.const) (t:Ast.typ) : Ll.ty * Ll.operand * stream =
    begin match cn.elt with
    | Ast.CInt i -> 
            if t.elt <> Ast.TInt then failwith "exp does not have
            the correct source type"
            else (cmp_typ t), (Ll.Const i), []
    | Ast.CBool b ->
            if t.elt <> Ast.TBool then failwith "exp does not have
            the correct source type"
            else (cmp_typ t), (i1_op_of_bool b), []

    | Ast.CNull ->
            match t.elt with
            | Ast.TRef r -> (cmp_typ t), Ll.Null, []
            | _ -> failwith "exp does not have the correct
            source type"
    end



(* Compile an expression ---------------------------------------------------- *)

(* Invariant: checks that exp has source type t, and returns the 
   corresponding LL type, an operand of that type, and a stream of
   instructions that computes the value of the operand.

   - the output LL ty should be (cmp_tmp t).                         

   - a NewArray expression must allocate the storage space for the 
     array (see the oat_alloc_array_dynamic) function, and generate
     iterator code for the array initializer

   - see the description of path expressions below                            *)

let cmp_binop bop ty op1 op2 :  insn =
    begin match bop with
      | Ast.Add _  -> Ll.Binop (Add, ty, op1, op2)
      | Ast.Mul _ -> Ll.Binop (Mul, ty, op1, op2)
      | Ast.Sub _ -> Ll.Binop (Sub, ty, op1, op2)
      | Ast.And _   -> Ll.Binop (And, ty, op1, op2)
      | Ast.IAnd _  -> Ll.Binop (And, ty, op1, op2) 
      | Ast.IOr _   -> Ll.Binop(Or, ty, op1, op2)
      | Ast.Or _    -> Ll.Binop(Or, ty, op1, op2)
      | Ast.Shl _   -> Ll.Binop(Shl, ty, op1, op2)
      | Ast.Shr _   -> Ll.Binop(Lshr, ty, op1, op2)
      | Ast.Sar _   -> Ll.Binop(Ashr, ty, op1, op2)
      | Ast.Eq  _  -> Ll.Icmp(Eq, ty, op1, op2)
      | Ast.Neq _  -> Ll.Icmp(Ne, ty, op1, op2)
      | Ast.Lt  _  -> Ll.Icmp(Slt, ty, op1, op2)
      | Ast.Lte _  -> Ll.Icmp(Sle, ty, op1, op2)
      | Ast.Gt  _  -> Ll.Icmp(Sgt, ty, op1, op2)
      | Ast.Gte _  -> Ll.Icmp(Sge, ty, op1, op2)
     end

let ty_of_bop bop : ty =
    match bop with
    | Ast.Add _  | Ast.Mul _ | Ast.Sub _ | Ast.Shl _ | Ast.Shr _ | Ast.Sar _
    | Ast.IAnd _ | Ast.IOr _ -> (cmp_typ (Ast.no_loc Ast.TInt))
    | Ast.Eq _ | Ast.Neq _ | Ast.Lt _ | Ast.Lte _ | Ast.Gt _ | Ast.Gte _ |
    Ast.And _ | Ast.Or _ -> (cmp_typ (Ast.no_loc Ast.TBool))

let rec cmp_exp (c:ctxt) (t:typ) (exp:exp) : (Ll.ty * Ll.operand * stream) =
    begin match exp.elt with
    | Ast.Const c -> (cmp_const c t)
    | Ast.Uop (uop,e) ->
            let (ans_ty, op, code) = (cmp_exp c t e) in
            let ans_id = (gensym "unop") in
            print_string ans_id;
            ((ans_ty, (Ll.Id ans_id), code >::I (ans_id, match uop with
                                | Ast.Neg _ -> Ll.Binop (Sub, ans_ty, i64_op_of_int 0, op)
                                | Ast.Lognot _ -> Ll.Icmp  (Eq, ans_ty, op, i1_op_of_bool false)
                                | Ast.Bitnot  _ -> Ll.Binop (Xor, ans_ty, op, i64_op_of_int (-1)))))
    
    | Ast.Bop (bop,e1,e2) -> 
            let (ans_ty1, op1, code1) = (cmp_exp c t e1) in
            let (ans_ty2, op2, code2) = (cmp_exp c t e1) in
            let ans_id = (gensym "bop") in 
            let my_ty = (ty_of_bop bop) in
            if my_ty <> (cmp_typ t) then failwith "Incorrect Type for BOP" 
            else 
                ((cmp_typ t), (Ll.Id ans_id), code1 >@ code2 >:: I (ans_id,
                (cmp_binop bop my_ty op1 op2)))
    
    end

(* Compile a path as a left-hand-side --------------------------------------- *)

(* Checks that p is a valid path for assignment, meaning that it is either:
    -  just an identifier (a.k.a. a Field) 
    -  or, a non-empty prefix path of array type followed by an Index:

    Example valid paths:
      Oat:     Ast path:
    x         [Field("x")]
    x[3]      [Field("x"); Index(Const(3L))]
    x[3][4]   [Field("x"); Index(Const(3L)); Index(Const(4))]
    f(17)[3]  [Call("f", [Const(17)]); Index(Const(3))]

   Invariant: the result of compiling a path as a lhs is the *source* type t
   of the path expression, an operand of type Ptr(cmp_typ t), and a stream
   that computes an address for the path  into the returned operand.         

   Note: To compile paths ending with and index, you can treat the prefix as 
   a path denoting an array _expression_.                                    

   
   Note: When compiling a _global_ identifier, it is necessary to introduce 
   a Bitcast operation because a globally-defined array or string constant
   might have a type that is more specific than the translation of its
   type given by cmp_typ.  For example, the global array initialized as
   {1, 2, 3}  must be declared at the top level as having type 
   {i64, [3 x i64]}, which records the length '3' as part of the type. 
   The translation type of Oat arrays is the type {i64, [0 x i64]}, which
   has static length '0' as the type.  To reconcile these differences, you
   must Bitcast the more specific type (found in the globals context) to
   the desired translation type.                                              *)
and cmp_path_lhs (c:ctxt) (p:path) : Ast.typ * Ll.operand * stream =
failwith "cmp_path_lhs not implemented"



(* Compile a path as an expression ------------------------------------------ *)

(* Checks that p is a valid path expression, meaning that it is either:
    -  just a well-typed call to a non-void function
    -  or, a non-empty path that is valid as a left-hand-side, from which 
       a value can be loaded.

    Example valid expression paths:
      Oat:     Ast path:
    f(17)     [Call("f", [Const(17)])]
    x         [Field("x")]
    x[3]      [Field("x"); Index(Const(3L))]
    x[3][4]   [Field("x"); Index(Const(3L)); Index(Const(4))]
    f(17)[3]  [Call("f", [Const(17)]); Index(Const(3))]

   Invariant: the result of compiling a path as an expression is the
   *source* type t of the path expression, an operand of type (cmp_typ
   t), and a stream that computes the value of the path expression into
   the returned operand.

   Note: if path is not just a call, you can compile it as a left-hand-side
   and the load from the resulting pointer.                                  *)
and cmp_path_exp (c:ctxt) (p:path) : Ast.typ * Ll.operand * stream =
  failwith "cmp_path_exp not implemented"



(* compile a statement ------------------------------------------------------ *)

(* Checks that the stmt is well typed and returns a new context and 
   a stream of LL instructions that implement the statment's behavior.

   - If the statement is a Return statement, it's form must match the
     rt argument.

   - If the statement is an SCall, it must be to a path identifying a 
     void function.  Note that this implies that the path has only one
     accessor.                                                                *)

and cmp_stmt (c:ctxt) (rt:rtyp) (stmt : Ast.stmt) : ctxt * stream =
    match stmt.elt with
    | Ast.Ret t -> match t with
               | Some exp -> 
                      begin match rt with
                      | Some r -> let (ty,op,str) = (cmp_exp c r exp) in
                                  begin match op with
                                  | Id i ->
                                          print_string i;
                                          let nc = add_local c (no_loc i) (i,r) in
                                          nc, str @ [T(Ll.Ret(ty, Some op))]
                                  | _ ->  c, str @ [T(Ll.Ret(ty, Some op))]
                                  end
                      | None -> failwith "non-void return type for void function"
                      end
               | None -> match rt with
                         | Some _ -> failwith "void return type for non-void function"
                         | None -> let t = Ll.Ret(Ll.Void, None) in c, [T t]

               
    





(* compile a block ---------------------------------------------------------- *)
and cmp_block (c:ctxt) (rt:rtyp) (stmts:Ast.block) : ctxt * stream =
  List.fold_left
    (fun (c,code) s ->
       let c, stmt_code = cmp_stmt c rt s in
       c, code >@ stmt_code) (c,[]) stmts






(* context translation types ------------------------------------------------ *)
type ll_funs    = (Ll.gid * Ll.fdecl) list 
type ll_globals = (Ll.gid * Ll.gdecl) list

(* compile a function declaration ------------------------------------------- *)

(* compiles a source function declaration, producing a target function 
   declaration and a list of global declarations.

   - this function may assume that the supplied context c has an 
     empty local context

   - the target function entry block code should translate the
     function arguments by placing them in alloca'ed stack slots and
     extending the local context accordingly

   - the returned control flow graph and hoisted globals should be 
     created by build_cfg                                                     *)

let cmp_fdecl (c:ctxt) {elt={rtyp; name; args; body}} :
  (Ll.gid * Ll.fdecl) * ll_globals =
  
  let rettyp = begin match rtyp with
    | Some x ->
       cmp_typ x
    | None -> Void
  end in
  
  let arg_typ  (x: typ * id) =
    begin match x with
      | (y, _) -> cmp_typ y
    end in
  
  let arg_id  (x: typ * id) =
    begin match x with
      | (_, y) -> y.elt
    end in

  let arg_typs = List.map arg_typ args in
  let func_fty = (arg_typs, rettyp) in
  let func_param = List.map arg_id args in
  
  let new_ctxt, strm = cmp_block c rtyp body in
  let func_cfg, func_llglobals = build_cfg strm in
  let beginning_block, other_blocks = func_cfg in
  
  let block_insns = beginning_block.insns in
  
  let alloca_args  (x: typ * id) =
    begin match x with
      | (x, y) ->
        let uid = gensym "alloca" in
        (uid, (Alloca (cmp_typ x)))::(gensym "alloca", (Store ((cmp_typ x), (Id y.elt), (Id uid))))::[]
    end
   in

   let new_block = {insns=((List.flatten (List.map alloca_args args)) @ block_insns); terminator=beginning_block.terminator} in
   let new_cfg = (new_block, other_blocks) in
   ((name.elt, {fty=func_fty; param=func_param; cfg=new_cfg}), func_llglobals)
                

(* compile all of the fdecls ------------------------------------------------ *)
let cmp_fdecls (c:ctxt) (p:Ast.prog) :  ll_funs * ll_globals =
  let f (x: gdecl) =
    begin match x with
      | Gvdecl y -> []
      | Gfdecl y -> (cmp_fdecl c y) ::[]
    end
  in
  
  let x, y = List.split (List.flatten (List.map f p)) in
  (x, (List.flatten y))

(* compile a global initializer --------------------------------------------- *)

(* Invariant: ty is the source type of the global value.  init is a
   _constant_ expression.  Outputs the target type, which should be
   correspond to the ginit_value, and ll_globals that initialize the
   statically-allocated memory block correctly.

   Unlike constant expressions that appear inside of functions (which
   require dynamic allocation of storage space), globally defined
   constants should simply translate to a sequence of appropriate LL 
   global initializers.  

   - for Null, Bool, and Int types the result type is simply 
     (cmp_tmp ty)
   
   - for String and Array types the resulting Ll.ty should correspond
     exactly to the ginit value's type, which may be more specific
     than (cmp_typ ty).  (Hint: the clang compiler's type errors
     can help you figure yout the exact types of the ginit values.)

   - global string declarations must translate to a global string
     constant, plus a reference to that constant.

   - global array declarations must include appropriate Oat-style
     array length information, and, like strings, must compile not
     only to the data, but to a pointer refering to that data.  The 
     static LL type of an array must use the correct length.  [See
     the corresponding note in cmp_path_lhs]                 

   - this function should fail if the initializer expression has
     incorrect type, or if the global initializer contains a
     non-constant expression.                                                 *)

let rec cmp_init (ty:Ast.typ) (init:Ast.exp) :  Ll.ty * Ll.ginit * ll_globals =
  let gid = gensym "constant" in

  let typ =
    begin match init.elt with
      | Const x ->
        begin match x.elt with
          | CArr a -> failwith "unimplemented"
          | _ -> cmp_typ ty
        end
      | _ -> failwith "non-constant expression"
    end in

  begin match init.elt with
    | Const x ->
      begin match x.elt with
        | CNull -> (typ, GNull, [(gid, (typ, GNull))])
        | CBool b -> 
          begin match b with
            | true -> (typ, (GInt 0L), [(gid, (typ, GInt 0L))])
            | false -> (typ, GInt 1L, [(gid, (typ, GInt 1L))])
          end
        | CInt i -> (typ, GInt i, [(gid, (typ, GInt i))])
        | CStr s -> let gid2 = gensym "constant" in
          (Ptr (Array (String.length s + 1, I8)),  GGid gid, [(gid, (Array (String.length s + 1, I8),  GString s)); (gid2, (Ptr (Array (String.length s + 1, I8)),  GGid gid))])
        | CArr a -> failwith "unimplemented"
      end
    | _ -> failwith "non-constant expression"
  end

(* compile the global context ----------------------------------------------- *)

(* compiles a source global declaration into a global context entry and 
   a sequence of LL globals                                                   *)
let gvdecl_typ {elt={ty; id; init}} : (id * global_binding) * ll_globals =
  let ll_ty, ginit, gs  = cmp_init ty init in
  (id, (id.elt, ty, ll_ty)), (id.elt, (ll_ty, ginit))::gs


(* compiles a source function type declaration into a function context entry  *)
let fdecl_typ {elt={rtyp; name; args}} : id * funs_binding =
  let ts = List.map fst args in
  (name, (name.elt, (ts, rtyp)))

(* produces the top-level global context suitable for typechecking/compiling
   each function declaration, as well as the globals needed to initialize
   global data declarations                                                   

   Oat programs consist of a sequence of global declarations
   containing data values and (possibly) mutually recursive function
   definitions.  Therefore, to typecheck a function body, it is
   necessary to first figure out the global context, which has the
   type information about all of the declarations.  

   Use gvdecl_typ and gfdecl_typ to complete this function.                   *)

let cmp_global_ctxt (p:Ast.prog) (c:ctxt) : ctxt * ll_globals =
  
  let gvll  (x: gdecl) =
    begin match x with
    | Gvdecl d ->
      let ret = gvdecl_typ d in
      begin match ret with
        | (_, x) -> x
      end
    | Gfdecl f  -> []
    end
  in

  let gvctxt  (x: gdecl) =
    begin match x with
    | Gvdecl d ->
      let ret = gvdecl_typ  d in

      begin match ret with
        | (x, _) -> 
          let str = begin match x with 
          | (s, _) -> s.elt
          end in

          let vars = begin match x with 
            | (_, v) -> v
          end in

          [(str,vars)]
      end
    | Gfdecl f  -> []
    end
  in

  let gfctxt  (x: gdecl) =
    begin match x with
    | Gvdecl d -> []
    | Gfdecl f  ->
      let ret = fdecl_typ  f in
      let str = begin match ret with
        | (s, _) -> s.elt
      end in
      
      let funs = begin match ret with
        | (_, y) -> y
      end in
      [(str, funs)]
    end
  in
  
  let llglob =  List.flatten (List.map gvll p) in
  let globvar =  List.flatten (List.map gvctxt p) in
  let globfun =  List.flatten (List.map gfctxt p) in
  let retctxt = {funs = (List.append globfun c.funs); global = (List.append globvar c.global); local = c.local} in
  (retctxt, llglob)

(* Oat initial context ------------------------------------------------------ *)

let prelude =
  [ "array_of_string",  ([ast_str],  Some(ast_array_typ ast_int))
  ; "string_of_array",  ([ast_array_typ ast_int], Some(ast_str))
  ; "length_of_string", ([ast_str],  Some(ast_int))
  ; "string_of_int",    ([ast_int],  Some(ast_str))
  ; "string_cat",       ([ast_str; ast_str], Some(ast_str))
  ; "print_string",     ([ast_str],  None)
  ; "print_int",        ([ast_int],  None)
  ; "print_bool",       ([ast_bool], None)
  ]

let init_ctxt =
  List.fold_left
    (fun c (s, fty) -> add_function c (no_loc s) (s, fty)) empty_ctxt 
    prelude

(* Compile a top-level program ---------------------------------------------- *)
let cmp_prog (p: Ast.prog) : Ll.prog =
  let c, gdecls = cmp_global_ctxt p init_ctxt in
  let (fdecls, hoisted_globals) = cmp_fdecls c p in
  { tdecls = []; gdecls=gdecls @ hoisted_globals;  fdecls; }


(* Oat LLVM prelude --------------------------------------------------------- *)

(* This is a string represeting the LLVM IR external declarations for
   the oat built-in functions.  These functions are implemented in
   runtime.c                                                                  *)
let oat_ll_prelude =
  let to_str (fn, (args, rtyp)) =
    let args_str = List.map (fun t -> string_of_ty (cmp_typ t)) args
                   |> String.concat ", "
    in
    let rtyp_str = string_of_ty (cmp_rtyp rtyp) in
    Printf.sprintf "declare %s @%s (%s)"
      rtyp_str fn args_str
  in
  let declares = List.map to_str prelude
               |> String.concat "\n"
  in
  Printf.sprintf 
  "target datalayout = \"e-m:o-i64:64-f80:128-n8:16:32:64-S128\"\n\n\
  ; ------------------------------------------------ prelude\n\n\
  ; internal oat functions (not available in source)\n\
  declare i64* @oat_malloc(i64)\n\
  declare {i64, [0 x i64]}* @oat_alloc_array (i64)\n\
  \n\
  ; oat 'builtin' functions\n\
  %s\n\
  ; --------------------------------------------------------\n\n\
  " declares

    
