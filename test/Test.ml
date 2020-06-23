open DiceLib
open OUnit2
open Core
open Util
open Compiler


let test_1 _ =
  let prog = "let x = flip 0.4 in x" in
  assert_feq 0.4 (parse_and_prob prog)

let test_not _ =
  let prog = "let x = flip 0.4 in !x" in
  assert_feq 0.6 (parse_and_prob prog)

let test_obs1 _ =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in x" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog)

let test_obs2 _ =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in !x" in
  assert_feq (0.06 /. 0.46) (parse_and_prob prog)

let test_tup1 _ =
  let prog = "let x = (flip 0.1, flip 0.4) in snd x" in
  assert_feq 0.4 (parse_and_prob prog)

let test_nestedtup _ =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in fst (snd x)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_nestedtup2 _ =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in ! fst (snd x)" in
  assert_feq 0.6 (parse_and_prob prog)

let test_ite1 _ =
  let prog = "if flip 0.4 then true else false" in
  assert_feq 0.4 (parse_and_prob prog)

let test_ite2 _ =
  let prog = "if flip 0.4 then flip 0.6 else false" in
  assert_feq 0.24 (parse_and_prob prog)

let test_ite3 _ =
  let prog = "if flip 0.4 then let z = observe false in flip 0.6 else false" in
  assert_feq 0.0 (parse_and_prob prog)

let test_int1 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in x == int(2, 1)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_int2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 0)) in x == int(2, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog)

let test_int3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 0) || x == int(2,1)) in x == int(2, 2)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_int4 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 1)) in x == int(2, 2)" in
  assert_feq (0.5 /. 0.6) (parse_and_prob prog)

let test_add1 _ =
  let prog = "let x = int(3, 0) + int(3, 1) in x == int(3, 1)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_add2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + int(2, 1) in x == int(2, 1)" in
  assert_feq 0.1 (parse_and_prob prog)

let test_add3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + discrete(1.0, 0.0, 0.0) in x == int(2, 1)" in
  assert_feq 0.4 (parse_and_prob prog)

let test_add4 _ =
  let prog = "let x = discrete(0.25, 0.25, 0.25, 0.25) + discrete(0.25, 0.25, 0.25, 0.25) in x == int(2, 1)" in
  assert_feq 0.25 (parse_and_prob prog)

let test_add5 _ =
  let prog = "
   let x = discrete(0.3, 0.1, 0.2, 0.2, 0.2) in
   let y = discrete(0.1, 0.3, 0.2, 0.2, 0.2) in
   let sum = x + y in
   let z = observe x == int(3, 1) in
   sum == int(3, 1)" in
  assert_feq 0.1 (parse_and_prob prog)

let test_add6 _ =
  let prog = "let x = discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125)
+ discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125) in x == int(3, 1)" in
  assert_feq 0.125 (parse_and_prob prog)

let test_sub1 _ =
  let prog = "let x = int(3, 0) - int(3, 1) in x == int(3, 7)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_sub2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) - int(2, 1) in x == int(2, 1)" in
  assert_feq 0.5 (parse_and_prob prog)

let test_sub3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) - discrete(0.0, 1.0, 0.0) in x == int(2, 1)" in
  assert_feq 0.5 (parse_and_prob prog)

let test_sub4 _ =
  let prog = "let x = discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125)
- discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125) in x == int(3, 1)" in
  assert_feq 0.125 (parse_and_prob prog)


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
   (x + y) < int(2, 2)" in
  assert_feq (23.0 /. 50.0) (parse_and_prob prog)

let test_op4 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   let tmp = observe (x + y) < int(2, 2) in
   x == y" in
  assert_feq (5.0 /. 23.0) (parse_and_prob prog)


let test_iff1 _ =
  let prog = "true <=> false" in
  assert_feq 0.0 (parse_and_prob prog)

let test_iff2 _ =
  let prog = "false <=> false" in
  assert_feq 1.0 (parse_and_prob prog)

let test_iff3 _ =
  let prog = "flip 0.1 <=> flip 0.4" in
  assert_feq 0.58 (parse_and_prob prog)


let test_xor1 _ =
  let prog = "true ^ false" in
  assert_feq 1.0 (parse_and_prob prog)

let test_xor2 _ =
  let prog = "false ^ false" in
  assert_feq 0.0 (parse_and_prob prog)

let test_xor3 _ =
  let prog = "flip 0.1 ^ flip 0.4" in
  assert_feq 0.42 (parse_and_prob prog)


let test_mul1 _ =
  let prog = "let x = int(3, 0) * int(3, 1) in x == int(3, 0)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_mul2 _ =
  let prog = "let x = int(3, 2) * int(3, 2) in x == int(3, 4)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_mul3 _ =
  let prog = "let x = int(3, 3) * int(3, 3) in x == int(3, 1)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_mul4 _ =
  let prog = "let x = int(4, 3) * int(4, 3) in x == int(4, 9)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_mul5 _ =
  let prog = "let x = int(4, 3) * int(4, 3) * int(4, 3) in x == int(4, 11)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_mul6 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5, 0.0) * int(2, 2) in x == int(2, 0)" in
  assert_feq 0.6 (parse_and_prob prog)

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

let test_fcall7 _ =
  let prog = "
    fun foo(test1: int(2)) {
      let k = observe !(test1 == int(2, 0)) in
      false
    }
    let f1 = discrete(0.1, 0.4, 0.5) in
    let tmp = foo(f1) in f1 == int(2, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog)

let test_caesar _ =
  let prog = "
    fun sendchar(key: int(2), observation: int(2)) {
      let gen = discrete(0.5, 0.25, 0.125, 0.125) in
      let enc = key + gen in
      observe observation == enc
    }
    let key = discrete(0.25, 0.25, 0.25, 0.25) in
    let tmp = sendchar(key, int(2, 0)) in
    let tmp = sendchar(key, int(2, 1)) in
    let tmp = sendchar(key, int(2, 2)) in
    let tmp = sendchar(key, int(2, 3)) in
    key == int(2, 0)" in
  assert_feq 0.25 (parse_and_prob prog)

let test_caesar_iterate _ =
  let prog = "
fun sendchar(arg: (int(2), int(2))) {
  let key = fst arg in
  let observation = snd arg in
  let gen = discrete(0.5, 0.25, 0.125, 0.125) in    // sample a foolang character
  let enc = key + gen in                            // encrypt the character
  let tmp = observe observation == enc in
  (key, observation + int(2, 1))
}
// sample a uniform random key: a=0, b=1, c=2, d=3
let key = discrete(0.25, 0.25, 0.25, 0.25) in
// observe the ciphertext cccc
let tmp = iterate(sendchar, (key, int(2, 2)), 4) in
key == int(2, 0)
" in
  assert_feq 0.25 (parse_and_prob prog)


let test_burglary _ =
  let prog = "
    let burglary = flip 0.001 in
    let earthquake = flip 0.002 in
    let alarm = if burglary then if earthquake then flip 0.95 else flip 0.94 else if earthquake then flip 0.29 else flip 0.001 in
    let john = 	if alarm then flip 0.9 else flip 0.05 in
    let mary = 	if alarm then flip 0.7 else flip 0.01 in
    let temp = observe john in
    let temp = observe mary in
    burglary" in
  assert_feq 0.284172 (parse_and_prob prog)

let test_alarm _ =
  let prog = In_channel.read_all "../benchmarks/baselines/alarm.dice" in
  assert_feq (2969983.0 /. 992160802.0) (parse_and_prob prog)

let test_murder _ =
  let prog = In_channel.read_all "../benchmarks/baselines/murderMystery.dice" in
  assert_feq (9.0 /. 569.0) (parse_and_prob prog)

let test_evidence1 _ =
  let prog = In_channel.read_all "../benchmarks/baselines/evidence1.dice" in
  assert_feq (1.0 /. 3.0) (parse_and_prob prog)

let test_evidence2 _ =
  let prog = In_channel.read_all "../benchmarks/baselines/evidence2.dice" in
  assert_feq (2.0 /. 3.0) (parse_and_prob prog)

let test_grass _ =
  let prog = In_channel.read_all "../benchmarks/baselines/grass.dice" in
  assert_feq (509.0 /. 719.0) (parse_and_prob prog)

let test_cancer _ =
  let prog = In_channel.read_all "../resources/cancer_test.dice" in
  assert_feq (42709.0 /. 200000.0) (parse_and_prob prog)

let test_caesar_2 _ =
  let prog = In_channel.read_all "../resources/caesar_test.dice" in
  assert_feq  (1113032.0 /. 315312455.0) (parse_and_prob prog)

let test_alarm_2 _ =
  (* the correct answer here is from ace *)
  let prog = In_channel.read_all "../resources/alarm_test.dice" in
  assert_feq 0.281037656 (parse_and_prob prog)

let test_pmc1 _ =
  let prog = In_channel.read_all "../resources/pmc1.dice" in
  assert_feq (1023.0 /. 2048.0) (parse_and_prob prog)

let test_pmc2 _ =
  let prog = In_channel.read_all "../resources/pmc2.dice" in
  assert_feq (31.0 /. 64.0) (parse_and_prob prog)



let test_double_flip _ =
  let prog = "
    let c1 = flip 0.5 in
    let c2 = flip 0.5 in
    c1 && c2
    " in
  assert_feq 0.25 (parse_and_prob prog)

let test_typecheck_1 _ =
  let prog = "
    let c1 = discrete(0.1, 0.4, 0.5) in
    let c2 = int(2, 1) in
    (c1 == c2) || (c1 != c2)
    " in
  assert_feq 1.0 (parse_and_prob prog)

let test_mod_sub _ =
  let prog = "
    let c1 = int(3, 0) in
    let c2 = int(3, 1) in
    (c1 - c2) == int(3, 2)" in
  assert_feq 1.0 (parse_and_prob prog)

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
  let prog = "let coin1 = if flip 0.5 then int(6, 10) else int(6, 25) in
let coin2 = if flip 0.5 then int(6, 10) else int(6, 25) in
let s1 = if flip(0.8) then coin1 else int(6, 0) in
let s2 = if flip 0.8 then coin2 + s1 else s1 in
let candy = s2 >= int(6, 15) in
let tmp = observe candy in
coin1 == int(6, 10)
" in assert_feq 0.45 (parse_and_prob prog)

let test_swap _ =
  let open Cudd in
  let mgr = Man.make_d () in
  let bdd1 = Bdd.newvar mgr in
  let bdd2 = Bdd.newvar mgr in
  let bdd3 = Bdd.newvar mgr in
  let bdd4 = Bdd.newvar mgr in
  let andbdd = Bdd.dand bdd1 bdd2 in
  let swapbdd = List.to_array [bdd3; bdd4] in
  let swapidx = List.to_array [Bdd.topvar bdd1; Bdd.topvar bdd2] in
  let swapped = Bdd.labeled_vector_compose andbdd swapbdd swapidx in
  OUnit2.assert_bool "Expected equal bdds" (Bdd.is_equal (Bdd.dand bdd3 bdd4) swapped)

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

  "test_sub1">::test_sub1;
  "test_sub2">::test_sub2;
  "test_sub3">::test_sub3;
  "test_sub4">::test_sub4;

  "test_iff1">::test_iff1;
  "test_iff2">::test_iff2;
  "test_iff3">::test_iff3;

  "test_xor1">::test_xor1;
  "test_xor2">::test_xor2;
  "test_xor3">::test_xor3;


  "test_mul1">::test_mul1;
  "test_mul2">::test_mul2;
  "test_mul3">::test_mul3;
  "test_mul4">::test_mul4;
  "test_mul5">::test_mul5;
  "test_mul6">::test_mul6;

  "test_fcall1">::test_fcall1;
  "test_fcall2">::test_fcall2;
  "test_fcall3">::test_fcall3;
  "test_fcall4">::test_fcall4;
  "test_fcall5">::test_fcall5;
  "test_fcall6">::test_fcall6;
  "test_fcall7">::test_fcall7;

  "test_caesar">::test_caesar;
  "test_alarm">::test_alarm;
  "test_alarm_2">::test_alarm_2;
  "test_murder">::test_murder;
  "test_evidence1">::test_evidence1;
  "test_evidence2">::test_evidence2;
  "test_grass">::test_grass;
  "test_cancer">::test_cancer;
  "test_op1">::test_op1;
  "test_op2">::test_op2;
  "test_op3">::test_op3;
  "test_op4">::test_op4;

  "test_alarm">::test_alarm;
  "test_coin">::test_coin;
  "test_burglary">::test_burglary;
  "test_double_flip">::test_double_flip;
  "test_typecheck">::test_typecheck_1;
  "test_caesar_iterate">::test_caesar_iterate;
  "test_pmc1">::test_pmc1;
  "test_pmc2">::test_pmc2;

  "test_swap">::test_swap;
]

let () =
  run_test_tt_main expression_tests;
