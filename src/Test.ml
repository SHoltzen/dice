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

let parse_and_prob ?debug e =
  let buf = Lexing.from_string e in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith ""
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith "" in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
   | _ -> ());
  CoreGrammar.get_prob (from_external_prog parsed)

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

let test_ite3 _ =
  let prog = "if flip 0.4 then let z = observe false in flip 0.6 else false" in
  assert_feq 0.0 (parse_and_prob prog)

let test_int1 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in x == int(3, 1)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_int2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(3, 0)) in x == int(3, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog)

let test_int3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(3, 0) || x == int(3,1)) in x == int(3, 2)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_add1 _ =
  let prog = "let x = int(3, 0) + int(3, 1) in x == int(3, 1)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_add2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + int(3, 1) in x == int(3, 1)" in
  assert_feq 0.1 (parse_and_prob prog)

let test_add3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + discrete(1.0, 0.0, 0.0) in x == int(3, 1)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_add4 _ =
  let prog = "let x = discrete(0.2, 0.2, 0.2, 0.2, 0.2) + discrete(0.2, 0.2, 0.2, 0.2, 0.2) in x == int(5, 1)" in
  assert_feq 0.2 (parse_and_prob prog)

let test_add5 _ =
  let prog = "
   let x = discrete(0.3, 0.1, 0.2, 0.2, 0.2) in
   let y = discrete(0.1, 0.3, 0.2, 0.2, 0.2) in
   let sum = x + y in
   let z = observe x == int(5, 1) in
   sum == int(5, 1)" in
  assert_feq 0.1 (parse_and_prob prog)

let test_fcall1 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(true) && foo(true)" in
  assert_feq 0.25 (parse_and_prob prog)

let test_fcall2 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(true) && foo(false)" in
  assert_feq 0.0 (parse_and_prob prog)

let test_fcall3 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(flip 0.5) && foo(flip 0.5)" in
  assert_feq 0.06250 (parse_and_prob prog)

let test_fcall4 _ =
  let prog = "
    fun foo(test: bool) {
      let tmp = observe test in
      true
    }
    let z = flip 0.5 in
    let tmp = foo(z) in
    z" in
  assert_feq 1.0 (parse_and_prob prog)

let test_fcall5 _ =
  let prog = "
    fun foo(test1: bool, test2: bool) {
      let k = observe test1 || test2 in
      false
    }
    let f1 = flip 0.4 in
    let f2 = flip 0.1 in
    let tmp = foo(f1, f2) in
    f1" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog)

let test_fcall6 _ =
  let prog = "
    fun foo(test1: (bool, bool)) {
      let k = observe (fst test1) || (snd test1) in
      false
    }
    let f1 = flip 0.4 in
    let tmp = foo((f1, flip 0.1)) in f1" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog)

let test_fcall6 _ =
  let prog = "
    fun foo(test1: int(3)) {
      let k = observe !(test1 == int(3, 0)) in
      false
    }
    let f1 = discrete(0.1, 0.4, 0.5) in
    let tmp = foo(f1) in f1 == int(3, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog)

let test_caesar _ =
  let prog = "
    fun sendChar(key: int(4), observation: int(4)) {
      let gen = discrete(0.5, 0.25, 0.125, 0.125) in
      let enc = key + gen in
      observe observation == enc
    }
    let key = discrete(0.25, 0.25, 0.25, 0.25) in
    let tmp = sendChar(key, int(4, 0)) in
    let tmp = sendChar(key, int(4, 0)) in
    let tmp = sendChar(key, int(4, 0)) in
    let tmp = sendChar(key, int(4, 0)) in
    let tmp = sendChar(key, int(4, 0)) in
    key == int(4, 0)" in
  assert_feq 0.96786389414 (parse_and_prob prog)



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
  "test_int1">::test_int1;
  "test_int2">::test_int2;
  "test_int3">::test_int3;
  "test_add1">::test_add1;
  "test_add2">::test_add2;
  "test_add3">::test_add3;
  "test_add4">::test_add4;
  "test_add5">::test_add5;
  "test_fcall1">::test_fcall1;
  "test_fcall2">::test_fcall2;
  "test_fcall3">::test_fcall3;
  "test_fcall4">::test_fcall4;
  "test_fcall5">::test_fcall5;
  "test_fcall6">::test_fcall6;
  "test_caesar">::test_caesar;
]

let () =
  run_test_tt_main expression_tests;


