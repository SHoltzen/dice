open OUnit2
open Core
open CoreGrammar
open Wmc
open BddUtil
open AddImpl

let run_compare test_ctx =
  let n = 13 in
  let stmt = List.map ~f:(fun i ->
      let xn = sprintf "x%d" i in
      let yn = sprintf "y%d" i in
      Seq([ Flip(yn, 1.0 /. (float_of_int (i+3)));
            Flip(xn, 1.0 /. (float_of_int (i+4)));
            Observe(Or(And(Not(Ident(yn)), Ident(xn)), And(Ident(yn), Not(Ident(xn)))))
        ])
    ) (List.init n (fun x -> x)) in
  Format.printf "prog: %s" (string_of_stmt (Seq(stmt)));
  Format.printf "%f" (AddImpl.prob (Seq(stmt)) (Ident("y0")))

let test_1 test_ctx =
  let prog =
    Seq([Flip("x", 0.5);
         If(Ident("x"),
            Flip("y", 0.5), Flip("y", 0.7));
         Assgn("z", And(Ident("x"), Ident("y")))])
  in
  Format.printf "%f" (AddImpl.prob prog (Ident("y")))
  (* let e1 = Let("x", Flip(0.1), AExpr(Ident("x"))) in
   * let ctx = new_context () in
   * let compiled = compile_expr ctx e1 in
   * let bdd = extract_bdd compiled in
   * dump_dot ctx.name_map bdd;
   * Format.printf "prob: %f" (wmc bdd ctx.weights) *)

(* Name the test cases and group them together *)
let expression_tests =
"suite">:::
[
  (* "test_1">::test_1; *)
  "test_1">::run_compare;
]

let () =
  run_test_tt_main expression_tests;


