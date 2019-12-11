open OUnit2
open Core
open CoreGrammar
open Wmc
open BddUtil
open Lexing
open Lexer
open Parser

let eps = 0.00001

let assert_feq f1 f2 =
  OUnit2.assert_equal ~cmp:(fun x y -> ((Float.abs (f1 -. f2)) < eps)) f1 f2
    ~printer:string_of_float

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


let parse_and_prob e =
  let buf = Lexing.from_string e in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith ""
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith "" in
  (* Format.printf "%s\n" (ExternalGrammar.string_of_eexpr parsed); *)
  let prog = CoreGrammar.from_external_expr parsed in
  CoreGrammar.get_prob prog

let test_1 test_ctx =
  let prog = "let x = flip 0.4 in x" in
  assert_feq 0.4 (parse_and_prob prog)

let test_not test_ctx =
  let prog = "let x = flip 0.4 in !x" in
  assert_feq 0.6 (parse_and_prob prog)

let test_obs1 test_ctx =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in x" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog)

let test_obs2 test_ctx =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in !x" in
  assert_feq (0.06 /. 0.46) (parse_and_prob prog)

let test_tup1 test_ctx =
  let prog = "let x = (flip 0.1, flip 0.4) in snd x" in
  assert_feq 0.4 (parse_and_prob prog)

let test_nestedtup test_ctx =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in fst (snd x)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_nestedtup2 test_ctx =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in ! fst (snd x)" in
  assert_feq 0.6 (parse_and_prob prog)

let test_ite1 test_ctx =
  let prog = "if flip 0.4 then true else false" in
  assert_feq 0.4 (parse_and_prob prog)

let test_ite2 test_ctx =
  let prog = "if flip 0.4 then flip 0.6 else false" in
  assert_feq 0.24 (parse_and_prob prog)

let test_ite3 test_ctx =
  let prog = "if flip 0.4 then let z = observe false in flip 0.6 else false" in
  assert_feq 0.0 (parse_and_prob prog)


(* Name the test cases and group them together *)
let expression_tests =
"suite">:::
[
  "test_1">::test_1;
  "test_not">::test_not;
  "test_obs1">::test_obs1;
  "test_obs2">::test_obs2;
  "test_tup1">::test_tup1;
  "test_nestedtup">::test_nestedtup;
  "test_nestedtup2">::test_nestedtup2;
  "test_ite1">::test_ite1;
  "test_ite2">::test_ite2;
  "test_ite3">::test_ite3;
]

let () =
  run_test_tt_main expression_tests;


