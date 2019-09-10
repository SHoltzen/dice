open OUnit2
open CoreGrammar
open Wmc
open BddUtil

let test_1 test_ctx =
  let e1 = Let("x", Flip(0.1), AExpr(Ident("x"))) in
  let ctx = new_context () in
  let compiled = compile_expr ctx e1 in
  let bdd = extract_bdd compiled in
  dump_dot ctx.name_map bdd;
  Format.printf "prob: %f" (wmc bdd ctx.weights)

(* Name the test cases and group them together *)
let expression_tests =
"suite">:::
[
  "test_1">::test_1;
]

let () =
  run_test_tt_main expression_tests;


