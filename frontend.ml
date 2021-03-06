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
   appen


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



let rec cmp_typ2 (t:Ast.typ) =
  match t.elt with
  | Ast.TBool  -> t_bool
  | Ast.TInt   -> t_int
  | Ast.TRef r -> (cmp_ref2 r)

and cmp_ref2 (r:Ast.ref) =
  match r.elt with
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_typ2 u)]

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
let gen_table = ((Hashtbl.create 100000) : ((string,(string*Ast.typ))  Hashtbl.t))

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
  | Ast.Neg | Ast.Bitnot -> (cmp_typ (Ast.no_loc Ast.TInt))
  | Ast.Lognot -> (cmp_typ (Ast.no_loc Ast.TBool))

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
            the correct source type int"
      else (cmp_typ t), (Ll.Const i), []
    | Ast.CBool b ->
      if t.elt <> Ast.TBool then failwith "exp does not have
            the correct source type bool"
      else (cmp_typ t), (i1_op_of_bool b), []

    | Ast.CNull ->
      begin match t.elt with
        | Ast.TRef r -> (cmp_typ t), Ll.Null, []
        | _ -> failwith "exp does not have the correct source type null"
      end
    | Ast.CStr str -> let btcst = (gensym "bitcast") in
      let str_id = gensym "str" in
      (cmp_typ t, (Id btcst), [G(str_id, (str_arr_typ str, Ll.GString str))] >@
                              [I(btcst, (Bitcast (Ptr (str_arr_typ str), Gid str_id, cmp_typ t)))])
    | Ast.CArr consts -> 
      let a_ty = begin match t.elt with
        | TRef x  ->
          begin match x.elt with
            | RArray t -> t
            | _ -> failwith "not an array"
          end
        | _ -> failwith "not an array"
      end in

      let op, strm = oat_alloc_array_static a_ty (List.length consts) in
      let cmp_consts (c: const) =
        let ty, op, strm = cmp_const c  a_ty in
        (ty, (op, strm))
      in

      let temp = List.map cmp_consts consts in
      let ty_lst, temp2 = List.split temp in
      let op_lst, strm_lst_lst = List.split temp2 in
      let strm_lst = List.flatten strm_lst_lst in

      let copy_consts (i: int) (c: const) =
        let gid = gensym "array" in
        let gid2 = gensym "array" in

        [I(gid, Gep (cmp_typ t, op, gep_array_index (i64_op_of_int i)))] @
        [I(gid2, Store(cmp_typ  a_ty, (List.nth op_lst i), Id gid))]
      in

      let cpy_strm_lst_lst = List.mapi copy_consts consts in
      let cpy_strm_lst =  List.rev (List.flatten cpy_strm_lst_lst ) in
      (cmp_typ t, op, strm >@ strm_lst >@ cpy_strm_lst)

    (*let my_ty = cmp_typ t in
      let na = (gensym "arr_op") in
      let codes = [I(na, (Ll.Alloca (cmp_typ t)))] in

      let rec find_type first =
      begin match first.elt with
        | Ast.CInt i -> Ast.no_loc (Ast.TInt)
        | Ast.CBool b -> Ast.no_loc (Ast.TBool)
        | Ast.CNull  -> Ast.no_loc (Ast.TRef(Ast.no_loc Ast.RString))
        | Ast.CStr s-> Ast.no_loc (Ast.TRef(Ast.no_loc Ast.RString))
        | Ast.CArr a-> (find_type (List.nth a 0))
      end in

      let my_typ = find_type fir in

      let rec init_array c ind cs =
      begin match c with
        | [] -> cs
        | x::y -> let uid = (gensym "elem") in
          init_array y (ind+1) cs >@ [I(uid,(Ll.Gep(my_ty, (Ll.Id (na)),
                                                    [   Const (0L);
                                                        Const (1L);
                                                        Const (Int64.of_int ind)
                                                    ])))] >@
          [I(gensym "store",(Store ((cmp_typ(my_typ)),(Ll.Const 0L),(Id uid))))] 
      end in

      let codes2 = init_array consts 0 codes in

          let fir = List.nth consts 0 in
          let my_typ = find_type fir in

          let rec init_array c ind cs =
              begin match c with
              | [] -> cs
              | x::y -> let uid = (gensym "elem") in
                        init_array y (ind+1) cs >@ [I(uid,(Ll.Gep(my_ty, (Ll.Id (na)),
                        [   Const (0L);
                            Const (1L);
                            Const (Int64.of_int ind)
                          ])))] >@
                          [I(gensym "store",(Store
                          ((cmp_typ(my_typ)),(Ll.Const 0L),(Id uid))))] 
              end in

          let codes = [I(na, (Ll.Alloca (cmp_typ2 t)))] in
          let codes2 = init_array consts 0 codes in

          (cmp_typ t),(Id na),codes2
      (cmp_typ t),(Id na),codes2*)
  end




(* Compile an expression ---------------------------------------------------- *)

(* Invariant: checks that exp has source type t, and returns the 
   corresponding LL type, an operand of that type, and a stream of
   instructions that computes the value of the operand.

   - the output LL ty should be (cmp_tmp t).                         

   - a NewArray expression must allocate the storage space for the 
     array (see the oat_alloc_array_dynamic) function, and generate
     iterator code for the array and generate
     iterator code for the array initializer
   - see the description of path expressions below                            *)

let cmp_binop bop ty op1 op2 :  insn =
  begin match bop with
    | Ast.Add -> Ll.Binop (Add, ty, op1, op2)
    | Ast.Mul -> Ll.Binop (Mul, ty, op1, op2)
    | Ast.Sub -> Ll.Binop (Sub, ty, op1, op2)
    | Ast.And -> Ll.Binop (And, ty, op1, op2)
    | Ast.IAnd -> Ll.Binop (And, ty, op1, op2) 
    | Ast.IOr -> Ll.Binop(Or, ty, op1, op2)
    | Ast.Or -> Ll.Binop(Or, ty, op1, op2)
    | Ast.Shl -> Ll.Binop(Shl, ty, op1, op2)
    | Ast.Shr -> Ll.Binop(Lshr, ty, op1, op2)
    | Ast.Sar -> Ll.Binop(Ashr, ty, op1, op2)
    | Ast.Eq  -> Ll.Icmp(Eq, ty, op1, op2)
    | Ast.Neq -> Ll.Icmp(Ne, ty, op1, op2)
    | Ast.Lt  -> Ll.Icmp(Slt, ty, op1, op2)
    | Ast.Lte -> Ll.Icmp(Sle, ty, op1, op2)
    | Ast.Gt  -> Ll.Icmp(Sgt, ty, op1, op2)
    | Ast.Gte -> Ll.Icmp(Sge, ty, op1, op2)
  end

let ty_of_bop bop : ty =
  match bop with
  | Ast.Add | Ast.Mul | Ast.Sub | Ast.Shl | Ast.Shr | Ast.Sar
  | Ast.IAnd | Ast.IOr -> (cmp_typ (Ast.no_loc Ast.TInt))
  | Ast.Eq | Ast.Neq | Ast.Lt | Ast.Lte | Ast.Gt | Ast.Gte |
    Ast.And | Ast.Or -> (cmp_typ (Ast.no_loc Ast.TBool))


let astty_of_bop bop =
  match bop with
  | Ast.Add | Ast.Mul | Ast.Sub | Ast.Shl | Ast.Shr | Ast.Sar
  | Ast.IAnd | Ast.IOr 
  | Ast.Eq | Ast.Neq | Ast.Lt | Ast.Lte | Ast.Gt | Ast.Gte  ->  (Ast.no_loc Ast.TInt)
  | Ast.And | Ast.Or -> (Ast.no_loc Ast.TBool)

let rec cmp_exp (c:ctxt) (t:typ) (exp:exp) : (Ll.ty * Ll.operand * stream) =
  begin match exp.elt with
    | Ast.Const c -> (cmp_const c t)
    | Ast.Path p -> 
      let (ast_ty, op, code) = cmp_path_exp c p in
      ((cmp_typ t), op, code)

    | Ast.Uop (uop,e) ->
      let (ans_ty, op, code) = (cmp_exp c t e) in
      let ans_id = (gensym "unop") in
      ((ans_ty, (Ll.Id ans_id), code >::I (ans_id, match uop with
         | Ast.Neg -> Ll.Binop (Sub, ans_ty, i64_op_of_int 0, op)
         | Ast.Lognot -> Ll.Icmp  (Eq, ans_ty, op, i1_op_of_bool false)
         | Ast.Bitnot  -> Ll.Binop (Xor, ans_ty, op, i64_op_of_int (-1)))))

    | Ast.Bop (bop,e1,e2) -> 
      let (ans_ty1, op1, code1) = (cmp_exp c (astty_of_bop bop) e1) in
      let (ans_ty2, op2, code2) = (cmp_exp c (astty_of_bop bop) e2) in
      let ans_id = (gensym "bop") in 
      let my_ty = (ty_of_bop bop) in
      (* if my_ty <> (cmp_typ t) then failwith "Incorrect Type for BOP" 
         else *)
      ((cmp_typ t), (Ll.Id ans_id), code1 >@ code2 >:: I (ans_id,
                                                          (cmp_binop bop ans_ty1 op1 op2)))
    | Ast.NewArr (typ, e1, id, e2) ->
      let (e1_ty, e1_op, e1_code) = (cmp_exp c (no_loc TInt) e1) in
      let op, strm = oat_alloc_array_dynamic typ e1_op in

      let arr_id = gensym "newarr" in
      let size = gensym "newarr" in
      let counter_alloca = (gensym "counter_alloca") in
      let cond_label = (gensym "cond") in
      let cond_op = gensym "cond_op" in
      let cond_op2 = gensym "cond_op2" in
      let merge_label = (gensym "merge") in
      let if_label = (gensym "if") in

      let nc = add_local c (id) (counter_alloca, no_loc TInt) in
      let exp_ty, exp_op, exp_strm = cmp_exp nc typ e2 in
      let gep_id = gensym "getelementptr" in
      let add_res = gensym "add" in

      (cmp_typ @@ ast_array_typ typ, op, e1_code >@  strm >@  [I (arr_id, Gep ((cmp_typ @@ ast_array_typ typ), op, gep_array_len))] >@
                                         [I(size, Load(Ptr I64, Id arr_id))] >@
                                         [I(counter_alloca, (Ll.Alloca (I64)))] >@
                                         [I(gensym "store", Store(I64, i64_op_of_int 0, Id counter_alloca))] >@ [T (Br (cond_label))] >@
                                         [L cond_label]  >@
                                         [I(cond_op, Load(Ptr I64, Id counter_alloca))] >@
                                         [I(cond_op2, Icmp (Slt, I64, Id cond_op, Id size))]  >@
                                         [T (Cbr (Id cond_op2, if_label, merge_label))] >@
                                         [L if_label] >@
                                         exp_strm >@ [I(gep_id, Gep (cmp_typ @@ ast_array_typ typ, op, gep_array_index (Id cond_op)))] >@
                                         [I(gensym "store", Store(cmp_typ typ, exp_op, Id gep_id))] >@ [I(add_res, Binop(Add, I64, Id cond_op, i64_op_of_int 1))] >@
                                         [I(gensym "store", Store(I64, Id add_res, Id counter_alloca))]
                                         >@ [T (Br cond_label)]>@ [L merge_label])

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

  let cmp_accessor (x: typ* string * stream)  (a: accessor) =
    begin match x with
      | (x, y, z) ->
        let t =
          begin match x.elt with
            | TRef x ->
              begin match x.elt with
                | RArray t -> t
                | _ -> failwith "incorrect type"
              end
            | _ -> failwith "incorrect type"
          end in

        let str = gensym "index" in
        let ll_ty, ll_op, ll_strm = begin match a.elt with
          | Index i ->
            cmp_exp c (no_loc TInt) i
          | _ -> failwith "not an index"
        end in

        let myuid = gensym "load_lhs" in
        (t, str, z @ (List.rev ll_strm)  @ [I(myuid, (Load (Ptr(cmp_typ x), Id y)))] @ [I(str, Gep (cmp_typ x, Id myuid, gep_array_index ll_op))])
    end
  in

  let cmp_accessor2 (x: typ* string * stream)  (a: accessor) =
    begin match x with
      | (x, y, z) ->
        let t =
          begin match x.elt with
            | TRef x ->
              begin match x.elt with
                | RArray t -> t
                | _ -> failwith "incorrect type"
              end
            | _ -> failwith "incorrect type"
          end in

        let str = gensym "index" in
        let ll_ty, ll_op, ll_strm = begin match a.elt with
          | Index i ->
            cmp_exp c (no_loc TInt) i
          | _ -> failwith "not an index"
        end in

        let myuid = gensym "loader" in
        let myuid2 = gensym "store" in
        let myuid3 = gensym  "store" in
        let bcinsn = [I(myuid2, (Ll.Alloca (cmp_typ (x))))] @ [I(myuid2,(Store((cmp_typ x), Id y, Id myuid2)))] in
        (t, str, z @ (List.rev ll_strm) @ bcinsn  @ [I(myuid, (Load (Ptr(cmp_typ x), Id myuid2)))] @ [I(str, Gep (cmp_typ x, Id myuid, gep_array_index ll_op))])
    end
  in


  begin match (List.nth p 0).elt with
    | Field id ->
      let lu = (List.mem_assoc id.elt c.local) in
      begin match lu with
        | false ->  let gu = (List.mem_assoc id.elt c.global) in
          begin match gu with
            | false -> let hu = (Hashtbl.mem gen_table id.elt) in
              begin match hu with
                | false -> failwith "Variable not declared"
                | true -> 
                  let (uid, ty)  = (Hashtbl.find gen_table id.elt) in
                  if List.length p == 1 then
                    (ty, Ll.Id uid, [])
                  else
                    let new_ty, new_str, new_strm = List.fold_left cmp_accessor (ty, uid, []) (List.tl p) in
                    (new_ty, (Id new_str), List.rev new_strm)
              end

            | true -> let (uid, ty, llty)  = (lookup_global id.elt c) in
              let myuid = (gensym "Bitcast") in
              let str_begin = [I(myuid, (Bitcast (Ptr llty, Ll.Gid uid, Ptr(cmp_typ ty))))] in
              if List.length p == 1 then               
                (ty, (Ll.Id myuid), str_begin)
              else
                let new_ty, new_str, new_strm = List.fold_left cmp_accessor (ty, myuid, str_begin) (List.tl p) in
                (new_ty, (Id new_str), List.rev new_strm)
          end
        | true ->  let (uid, ty)  = (lookup_local id.elt c) in
          if List.length p == 1 then
            (ty, Ll.Id uid, [])
          else
            let new_ty, new_str, new_strm = List.fold_left cmp_accessor (ty, uid, []) (List.tl p) in
            (new_ty, (Id new_str), List.rev new_strm)
      end
    | Call (id, explist) -> let (t,o,s) = cmp_path_exp2 c p in (t,o,s)
                            (*
                            begin match o with
                            | Id u ->
                            let new_ty, new_str, new_strm = List.fold_left cmp_accessor2 (t, u, []) (List.tl p) in
                            (new_ty, (Id new_str), s >@ (List.rev new_strm))
                            | Gid g ->
                            let new_ty, new_str, new_strm = List.fold_left cmp_accessor2 (t, g, []) (List.tl p) in
                            (new_ty, (Id new_str), s >@ (List.rev new_strm))
                            end 
                            *)
    | _ -> failwith "invalid path"

  end

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


  let cmp_accessor2 (x: typ* string * stream)  (a: accessor) =
    begin match x with
      | (x, y, z) ->
        let t =
          begin match x.elt with
            | TRef x ->
              begin match x.elt with
                | RArray t -> t
                | _ -> failwith "incorrect type"
              end
            | _ -> failwith "incorrect type"
          end in

        let str = gensym "index" in
        let ll_ty, ll_op, ll_strm = begin match a.elt with
          | Index i ->
            cmp_exp c (no_loc TInt) i
          | _ -> failwith "not an index"
        end in

        let myuid = gensym "loader" in
        let myuid2 = gensym "store" in
        let myuid3 = gensym  "store" in
        let myuid4  = gensym "load_cmp_exp" in

        let deref =  [I(myuid4,(Load(Ptr(cmp_typ t), Id str)))] in

        let bcinsn = [I(myuid2, (Ll.Alloca (cmp_typ (x))))] @ [I(myuid2,(Store((cmp_typ x), Id y, Id myuid2)))] in
        (t, myuid4, z @ List.rev ll_strm @ bcinsn  @ [I(myuid, (Load (Ptr(cmp_typ x), Id myuid2)))] @ [I(str, Gep (cmp_typ x, Id myuid, gep_array_index ll_op))] 
                    @ deref)
    end
  in


  begin match (List.nth p 0).elt with
    | Field id ->

      let ast_typ, op, str = cmp_path_lhs c p in
      let uid = (gensym "load_field_id") in

      ast_typ, (Id uid), str >::I(uid, (Load (Ptr (cmp_typ ast_typ), op)))
    | Call (id, lst) -> 

      let gid, (atyplst, rtyp) = lookup_function id.elt c in    
      let f (i: int)  (x: Ast.exp) =
        let ty, op, str = cmp_exp c (List.nth atyplst i) x  in
        (ty, (op, str)) in

      let typ_lst, temp  = List.split(List.mapi f lst) in
      let op_lst, strlst_lst = List.split temp in
      let str_lst = List.flatten (List.rev strlst_lst) in
      let uid = gensym "caller" in

      let ll_rtyp =
        match rtyp with
        | None -> failwith "can't be void"
        | Some r -> cmp_typ r
      in

      let call_elt = I(uid, Call(ll_rtyp, Gid gid, (List.combine typ_lst op_lst))) in
      let ast_typ =
        match rtyp with
        | None -> failwith "can't have void function"
        | Some r -> r
      in

      if (List.length p) = 1  then begin 
        (ast_typ, Id uid, str_lst >@ [call_elt])
      end

      else 
        let new_ty, new_str, new_strm = List.fold_left cmp_accessor2 (ast_typ, uid, []) (List.tl p) in
        (new_ty, (Id new_str), str_lst >@ [call_elt] >@ (List.rev new_strm))

    | _ -> failwith "invalid type for 0th element"

  end


and cmp_path_exp2 (c:ctxt) (p:path) : Ast.typ * Ll.operand * stream =


  let cmp_accessor2 (x: typ* string * stream)  (a: accessor) =
    begin match x with
      | (x, y, z) ->
        let t =
          begin match x.elt with
            | TRef x ->
              begin match x.elt with
                | RArray t -> t
                | _ -> failwith "incorrect type"
              end
            | _ -> failwith "incorrect type"
          end in

        let str = gensym "index" in
        let ll_ty, ll_op, ll_strm = begin match a.elt with
          | Index i ->
            cmp_exp c (no_loc TInt) i
          | _ -> failwith "not an index"
        end in

        let myuid = gensym "loader" in
        let myuid2 = gensym "store" in
        let myuid3 = gensym  "store" in
        let bcinsn = [I(myuid2, (Ll.Alloca (cmp_typ (x))))] @ [I(myuid2,(Store((cmp_typ x), Id y, Id myuid2)))] in
        (t, str, z @ ll_strm @ bcinsn  @ [I(myuid, (Load (Ptr(cmp_typ x), Id myuid2)))] @ [I(str, Gep (cmp_typ x, Id myuid, gep_array_index ll_op))])
    end
  in


  begin match (List.nth p 0).elt with
    | Field id ->

      let ast_typ, op, str = cmp_path_lhs c p in
      let uid = (gensym "load_field_id") in

      ast_typ, (Id uid), str >::I(uid, (Load (Ptr (cmp_typ ast_typ), op)))
    | Call (id, lst) -> 


      let gid, (atyplst, rtyp) = lookup_function id.elt c in    
      let f (i: int)  (x: Ast.exp) =
        let ty, op, str = cmp_exp c (List.nth atyplst i) x  in
        (ty, (op, str)) in

      let typ_lst, temp  = List.split(List.mapi f lst) in
      let op_lst, strlst_lst = List.split temp in
      let str_lst = List.flatten (List.rev strlst_lst) in
      let uid = gensym "calller" in

      let ll_rtyp =
        match rtyp with
        | None -> failwith "can't be void"
        | Some r -> cmp_typ r
      in

      let call_elt = I(uid, Call(ll_rtyp, Gid gid, (List.combine typ_lst op_lst))) in
      let ast_typ =
        match rtyp with
        | None -> failwith "can't have void function"
        | Some r -> r
      in

      if (List.length p) = 1  then begin 
        (ast_typ, Id uid, str_lst >@ [call_elt])
      end

      else 
        let new_ty, new_str, new_strm = List.fold_left cmp_accessor2 (ast_typ, uid, []) (List.tl p) in
        (new_ty, (Id new_str), str_lst >@ [call_elt] >@ (List.rev new_strm))




    | _ -> failwith "invalid type for 0th element"

  end





let rec cmp_decls c rt d ans: ctxt*stream = 
  begin match d with
    | [] -> c, ans
    | d::rest ->
      let d_cont = d.elt in
      let new_id = (gensym d_cont.id.elt) in
      Hashtbl.add gen_table d_cont.id.elt (new_id,d_cont.ty);
      let new_d = Ast.no_loc {ty = d_cont.ty; id = Ast.no_loc(new_id); init = d_cont.init } in 
      let (c1, s) = cmp_stmt c rt (Ast.no_loc(Ast.Decl new_d)) in
      (cmp_decls c1 rt rest (ans >@ s))
  end


(* compile a statement ------------------------------------------------------ *)

(* Checks that the stmt is well typed and returns a new context and 
   a stream of LL instructions that implement the statment's behavior.

   - If the statement is a Return statement, it's form must match the
     rt argument.

   - IfLthe statement is an SCall, it must be to a path identifying a 
     void function.  Note that this implies that the path has only one
     accessor.                                                                *)

and print_string_of_elt elt = 
  let s = string_of_elt elt in
  print_string s

and cmp_stmt (c:ctxt) (rt:rtyp) (stmt : Ast.stmt) : ctxt * stream =
  match stmt.elt with
  | Ast.Ret t -> 
    begin match t with
      | Some exp -> 
        begin match rt with
          | Some r -> let (ty,op,str) = (cmp_exp c r exp) in
            begin match op with
              | Id i ->
                (* let nc = add_local c (no_loc i)
                 * (i,r) in*)
                c, str >@  [T(Ll.Ret (ty, Some op))]
              | _ ->  c, str >@ [T(Ll.Ret(ty, Some op))]
            end
          | None -> failwith "non-void return type for void function"
        end
      | None -> begin match rt with
          | Some _ -> failwith "void return type for non-void function"
          | None -> let t = Ll.Ret(Ll.Void, None) in c, [T t]
        end
    end
  | Ast.If (e, b1, b2) -> let (t1, o1, s1) = (cmp_exp c (Ast.no_loc Ast.TBool) e) in
    c, s1 >@ (ifloop c rt o1 b1 b2)


  | Ast.While (e, b1) -> let (t1, o1, s1) = (cmp_exp c (Ast.no_loc Ast.TBool) e) in
    c,(whileloop c rt o1 b1 s1) 


  | Ast.For (d,e,s,b) -> let (c0,codes) = (cmp_decls c rt d []) in
    let (t,o,exp) = begin match e with
      | None -> (cmp_const (Ast.no_loc (Ast.CBool true)) (Ast.no_loc (Ast.TBool)))
      | Some ex -> (cmp_exp c0 (Ast.no_loc Ast.TBool) ex)
    end in
    let (c1, stcode) = begin match s with
      | None -> c0,[]
      | Some st -> (cmp_stmt c0 rt st)
    end in


    let _,e_b1 = cmp_block c1 rt b in
    let if_label = (gensym "if") in
    let cond_label = (gensym "cond") in
    let merge_label = (gensym "merge") in


    c1, codes >@
        [T (Br (cond_label))] >@
        [L cond_label]  >@ exp >@
        [T (Cbr (o, if_label, merge_label))] >@
        [L if_label] >@ e_b1 >@ stcode >@[T (Br cond_label)]>@ 
        [L merge_label]





  | Ast.Assn (p,e) ->
    let (t1, o1, s1) = (cmp_path_lhs c p) in
    let (t2, o2, s2) = (cmp_exp c t1 e) in

    c, s1>@s2>@[I(gensym "Assn", (Store (t2, o2, o1)))]

  | Ast.SCall p -> 
    begin match (List.nth p 0).elt with
      | Call (id, lst) -> 
        let gid, (atyplst, rtyp) = lookup_function id.elt c in    
        let f (i: int)  (x: Ast.exp) =
          let ty, op, str = cmp_exp c (List.nth atyplst i) x  in
          (ty, (op, str)) in

        let typ_lst, temp  = List.split(List.mapi f lst) in
        let op_lst, str_lst_lst = List.split temp in
        let str_lst = List.flatten (List.rev str_lst_lst) in
        let uid = gensym "scall" in

        let ll_rtyp =
          begin match rtyp with
            | None -> Void
            | Some r -> cmp_typ r
          end
        in

        let call_elt = I(uid, Call(ll_rtyp, Gid gid, (List.combine typ_lst op_lst))) in
        (c, str_lst >@ [call_elt])

      | _ -> failwith "illegal first element for scall"
    end


  | Ast.Decl d ->
    let dec = d.elt in
    let lu = (List.mem_assoc dec.id.elt c.local) in
    begin match lu with
      | false -> let (ty, op, str) = (cmp_exp c dec.ty dec.init) in
        (*let nc0 = begin match dec.ty.elt with
          | Ast.TRef r -> begin match r.elt with
              | Ast.RString -> begin match dec.init.elt with
                  | Ast.Const co ->begin match co.elt with
                      |Ast.CStr str -> print_endline "HERHEHE";
                        (add_global c dec.id ((dec.id.elt), dec.ty, (str_arr_typ str)))
                      | _ -> c
                    end
                  | _  -> c
                end
              | _ -> c
            end
          | _ -> c
          end in*)

        begin match op with
          | Id i -> let nc = add_local c (dec.id) (dec.id.elt, dec.ty) in
            nc,  str>@[I(dec.id.elt, (Ll.Alloca (cmp_typ dec.ty)))]>@ [I(gensym "store",(Store ((cmp_typ dec.ty), op,(Id dec.id.elt))))] 
          | _ ->    let nc = add_local c (dec.id) (dec.id.elt, dec.ty) in
            nc, str>@[I(dec.id.elt, (Ll.Alloca (cmp_typ dec.ty)))]>@ [I(gensym "store",(Store ((cmp_typ dec.ty), op, (Id dec.id.elt))))] 
        end

      | _ -> failwith "Variable exists in local context"
    end
  | _ -> failwith "unimplemented"




and ifloop c rt exp b1 b2 : stream =
  let _,e_b1 = cmp_block c rt b1 in
  if List.length b2 <> 0 then begin
    let _,e_b2 = cmp_block c rt b2 in
    let if_label = (gensym "if") in
    let else_label = (gensym "else") in
    let merge_label = (gensym "merge") in

    [T (Cbr (exp, if_label, else_label))] >@
    [L if_label] >@ e_b1 >@ [T (Br merge_label)] >@ 
    [L else_label] >@ e_b2 >@ [T (Br merge_label)] >@
    [L merge_label]

  end

  else begin

    let if_label = (gensym "if") in
    let merge_label = (gensym "merge") in

    [T (Cbr (exp, if_label, merge_label))] >@
    [L if_label] >@ e_b1 >@ [T (Br merge_label)]>@ 
    [L merge_label]
  end

and whileloop c rt exp b1 c1: stream =
  let _,e_b1 = cmp_block c rt b1 in
  let if_label = (gensym "if") in
  let cond_label = (gensym "cond") in
  let merge_label = (gensym "merge") in
  (* [L cond_label] >@ c1 >@  
     [T (Cbr (exp, if_label, merge_label))] >@
     [L if_label] >@ e_b1 >@ [T (Br cond_label)]>@
     [L merge_label]*)
  [] >@
  [T (Br (cond_label))] >@
  [L cond_label]  >@ c1 >@
  [T (Cbr (exp, if_label, merge_label))] >@
  [L if_label] >@ e_b1 >@ [T (Br cond_label)]>@ 
  [L merge_label]



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

  let alloca_args2  (x: typ * id) =
    begin match x with
      | (x, y) ->
        let uid = gensym "alloca" in
        I(uid, (Alloca (cmp_typ x)))::I(gensym "alloca", (Store ((cmp_typ x), (Id y.elt), (Id uid))))::[]
    end
  in

  let args_elt2 =  (List.map alloca_args2 args) in

  let uid_lst (i: int) (x: elt list) =
    begin match (List.nth x 0) with
      | I (uid, y) ->
        begin match (List.nth args i) with
          | (typ, id) -> (id, uid, typ) 
        end
      | _ -> failwith "not an I"
    end in

  let update_ctxt (c: ctxt) (x: Ast.id * string * Ast.typ) =
    begin match x with 
      | (id, str, typ) -> add_local c id (str, typ)
    end
  in

  let nc = List.fold_left update_ctxt c (List.mapi uid_lst args_elt2) in
  let new_ctxt, strm = cmp_block nc rtyp body in
  (* List.iter (print_string_of_elt) strm; *)
  let func_cfg, func_llglobals = build_cfg (List.rev (List.flatten args_elt2) >@ strm) in
  let beginning_block, other_blocks = func_cfg in
  ((name.elt, {fty=func_fty; param=func_param; cfg=func_cfg}), func_llglobals)


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

  begin match init.elt with
    | Const x ->
      begin match x.elt with
        | CNull -> (cmp_typ ty, GNull, [(gid, (cmp_typ ty, GNull))])
        | CBool b -> 
          begin match b with
            | true -> (cmp_typ ty, (GInt 1L), [(gid, (cmp_typ ty, GInt 1L))])
            | false -> (cmp_typ ty, GInt 0L, [(gid, (cmp_typ ty, GInt 0L))])
          end
        | CInt i -> (cmp_typ ty, GInt i, [(gid, (cmp_typ ty, GInt i))])
        | CStr s -> let gid2 = gensym "constant" in
          Ptr(str_arr_typ s),  GGid gid, [(gid, (str_arr_typ s,  GString s))]
        | CArr a ->
          let a_ty = begin match ty.elt with
            | TRef x  ->
              begin match x.elt with
                | RArray t -> t
                | _ -> failwith "not an array"
              end
            | _ -> failwith "not an array"
          end in
          let a_ll_ty, _, _ = cmp_init a_ty (no_loc (Const (List.nth a 0))) in
          let f (a: const) =
            let x, y, z = cmp_init a_ty (no_loc (Const a)) in
            (x, (y, z))
          in
          let lst = List.map f a in
          let array_ll_ty, temp = List.split lst in
          let array_ginit,temp_2_globals = List.split temp in
          let array_gdecls = List.combine array_ll_ty array_ginit in
          let array_globals = (List.flatten temp_2_globals) in
          let gid2 = gensym "array" in
          let gid3 = gensym "array"in
          let array_globals_2 = array_globals
                                @ [(gid, (Struct[I64; Array (List.length a, a_ll_ty)],
                                          GStruct [(I64, GInt (Int64.of_int (List.length a)));
                                                   (Array (List.length a, a_ll_ty), GArray array_gdecls)]))]
          in
          (Ptr(Struct [I64; Array (List.length a, a_ll_ty)]), GGid gid, array_globals_2)    
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


