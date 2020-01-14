open OUnit2
open Core
open Util

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

let test_int4 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(3, 1)) in x == int(3, 2)" in
  assert_feq (0.5 /. 0.6) (parse_and_prob prog)

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

let test_op1 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   x < y" in
  assert_feq (3.0 /. 20.0) (parse_and_prob prog)

let test_op2 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   x <= y" in
  assert_feq (7.0 /. 20.0) (parse_and_prob prog)

let test_op3 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   (x + y) < int(4, 2)" in
  assert_feq (23.0 /. 50.0) (parse_and_prob prog)

let test_op4 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   (x * y) < int(4, 2)" in
  assert_feq (31.0 /. 50.0) (parse_and_prob prog)

let test_op5 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   let tmp = observe (x + y) < int(4, 2) in
   x == y" in
  assert_feq (5.0 /. 23.0) (parse_and_prob prog)

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
    let tmp = sendChar(key, int(4, 1)) in
    let tmp = sendChar(key, int(4, 2)) in
    let tmp = sendChar(key, int(4, 3)) in
    key == int(4, 0)" in
  assert_feq 0.25 (parse_and_prob prog)

let test_alarm _ =
  let prog = In_channel.read_all "benchmarks/baselines/alarm.dice" in
  assert_feq (2969983.0 /. 992160802.0) (parse_and_prob prog)

let test_murder _ =
  let prog = In_channel.read_all "benchmarks/baselines/murderMystery.dice" in
  assert_feq (9.0 /. 569.0) (parse_and_prob prog)

let test_evidence1 _ =
  let prog = In_channel.read_all "benchmarks/baselines/evidence1.dice" in
  assert_feq (1.0 /. 3.0) (parse_and_prob prog)

let test_evidence2 _ =
  let prog = In_channel.read_all "benchmarks/baselines/evidence2.dice" in
  assert_feq (2.0 /. 3.0) (parse_and_prob prog)

let test_grass _ =
  let prog = In_channel.read_all "benchmarks/baselines/grass.dice" in
  assert_feq (509.0 /. 719.0) (parse_and_prob prog)

let test_cancer _ =
  let prog = In_channel.read_all "resources/cancer_test.dice" in
  assert_feq (42709.0 /. 200000.0) (parse_and_prob prog)

let test_caesar_2 _ =
  let prog = In_channel.read_all "resources/caesar_test.dice" in
  assert_feq  (1113032.0 /. 315312455.0) (parse_and_prob prog)

let test_alarm _ =
  let prog = In_channel.read_all "resources/alarm_test.dice" in
  assert_feq 0.281037656 (parse_and_prob prog)

let test_coin _ =
  (* equivalent psi program:
def main() {
  coin1 := 0;
  if(flip (0.5)) {
        coin1 = 10;
  } else {
        coin1 = 25;
  }
  coin2 := 0;
  if(flip(0.5)) {
    coin2 = 10;
  } else {
    coin2 = 25;
  }
  s1 := 0;
  s2 := 0;
  if(flip(0.8)) { s1 = coin1;  } else { s1 = 0 }
  if(flip(0.8)) { s2 = coin2 + s1; } else { s2 = s1; }
  candy := s2 >= 15;
  observe(candy);
  return coin1 == 10;
}
  *)
  let prog = "let coin1 = if flip 0.5 then int(51, 10) else int(51, 25) in
let coin2 = if flip 0.5 then int(51, 10) else int(51, 25) in
let s1 = if flip(0.8) then coin1 else int(51, 0) in
let s2 = if flip 0.8 then coin2 + s1 else s1 in
let candy = s2 >= int(51, 15) in
let tmp = observe candy in
coin1 == int(51, 10)
" in assert_feq 0.45 (parse_and_prob prog)



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
  "test_int4">::test_int4;
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
  "test_alarm">::test_alarm;
  "test_murder">::test_murder;
  "test_evidence1">::test_evidence1;
  "test_evidence2">::test_evidence2;
  "test_grass">::test_grass;
  "test_cancer">::test_cancer;
  "test_op1">::test_op1;
  "test_op2">::test_op2;
  "test_op3">::test_op3;
  "test_op4">::test_op4;
  "test_op5">::test_op5;
  "test_alarm">::test_alarm;
  "test_coin">::test_coin;
]

let () =
  run_test_tt_main expression_tests;
