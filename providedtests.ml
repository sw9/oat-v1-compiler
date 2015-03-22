open Ast
open Astlib
open Assert
open Driver

(* Do NOT modify this file -- we will overwrite it with our *)
(* own version when we test your project.                   *)

(* These tests will be used to grade your assignment *)

let assert_eq_ast (f: 'a -> 'a -> bool) (x: 'a) (y: unit -> 'a) : assertion =
  fun () -> if f x (y ())  then () else failwith "not equal"

let parse_test parse compare code ast =
  let lexbuf = Lexing.from_string code in
  assert_eq_ast compare ast (fun () -> (parse Lexer.token lexbuf))

let exp_test code ast = parse_test Parser.exp_top eq_exp code ast
let stmt_test code ast = parse_test Parser.stmt_top eq_stmt code ast

let parse_consts =
  [("self parse consts test one", parse_test Parser.const eq_const "{true, true,
  false}" (no_loc (CArr [no_loc (CBool true); no_loc (CBool true); no_loc (CBool false)])))
  ; ("self parse consts test two", parse_test Parser.const eq_const "{null, null, null}"
      (no_loc (CArr [no_loc (CNull); no_loc (CNull); no_loc (CNull)])))
  ; ("parse exp test one", exp_test "new string[3]{ i => i}" (no_loc (NewArr
  (no_loc (TRef (no_loc (RString))),no_loc (Const (no_loc (CInt 3L))),no_loc ("i"),no_loc (Path ([ no_loc (Field (no_loc ("i"))) ]))))))
  ; ("parse exp test two", exp_test "new int[][][3]{ i => new int[2]{ i => 0 }}" (no_loc (NewArr (no_loc (TRef (no_loc ((RArray (no_loc (TRef (no_loc ((RArray (no_loc (TInt))))))))))),no_loc (Const (no_loc (CInt 3L))),no_loc ("i"),no_loc (NewArr (no_loc (TInt),no_loc (Const (no_loc (CInt 2L))),no_loc ("i"),no_loc (Const (no_loc (CInt 0L)))))))))
  
  ;("parse consts test one", parse_test Parser.const eq_const "null" (no_loc CNull))
  ; ("parse consts test two", parse_test Parser.const eq_const "42" (no_loc (CInt 42L)))
  ; ("parse consts test three", parse_test Parser.const eq_const "true" (no_loc (CBool true)))
  ; ("parse consts test four", parse_test Parser.const eq_const "false" (no_loc (CBool false)))
  ; ("parse consts test seven", parse_test Parser.const eq_const "{1, 2, 3}"
      (no_loc (CArr [no_loc (CInt 1L); no_loc (CInt 2L); no_loc (CInt 3L)])))
  ; ("parse stmt test 9", stmt_test "if(j<n){}" (no_loc
  (If (no_loc (Bop (Lt,no_loc (Path ([ no_loc (Field (no_loc ("j"))) ])),no_loc
  (Path ([ no_loc (Field (no_loc ("n"))) ])))),[],[  ]))))
  
  ]

let stmt_test code ast = parse_test Parser.stmt_top eq_stmt code ast
let parse_tests = parse_consts

let oat_file_test path args =
  let _ = Platform.verb @@ Printf.sprintf "** Processing: %s\n" path in
  
  let output_path = !Platform.output_path in
  let dot_ll_file = Platform.gen_name output_path "test" ".ll" in
  let exec_file = Platform.gen_name output_path "exec" "" in
  let tmp_file = Platform.gen_name output_path "tmp" ".txt" in  

  let oat_ast = parse_oat_file path in
  let ll_ast = Frontend.cmp_prog oat_ast in
  let ll_str = Driver.string_of_ll_ast path ll_ast in
  let _ = write_file dot_ll_file ll_str in
  let _ = Platform.link (dot_ll_file::["runtime.c"]) exec_file in

  let result = Driver.run_program args exec_file tmp_file in
  let _ = Platform.sh (Printf.sprintf "rm -f %s %s %s" dot_ll_file exec_file tmp_file) Platform.ignore_error in
  let _ = Platform.verb @@ Printf.sprintf "** Executable output:\n%s\n" result in
  result

let executed_oat_file tests =
  List.map (fun (path, args, ans) ->
      (path ^ " args: " ^ args), assert_eqf (fun () -> oat_file_test path args) ans)
    tests



let tests : suite =
  [ Test("self tests", parse_tests);
  ]

let provided_tests : suite = tests
