open DiceLib
open OUnit2
open Core
open Util
open Compiler


let test_1 _ =
  let prog = "let x = flip 0.4 in x" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_not test_ctx =
  let prog = "let x = flip 0.4 in !x" in
  assert_feq 0.6 (parse_and_prob prog);
  assert_feq 0.6 (parse_optimize_and_prob prog)

let test_obs1 _ =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in x" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog);
  assert_feq (0.4 /. 0.46) (parse_optimize_and_prob prog)

let test_obs2 _ =
  let prog = "let x = flip 0.4 in let y = flip 0.1 in let z = observe x || y in !x" in
  assert_feq (0.06 /. 0.46) (parse_and_prob prog);
  assert_feq (0.06 /. 0.46) (parse_optimize_and_prob prog)

let test_tup1 _ =
  let prog = "let x = (flip 0.1, flip 0.4) in snd x" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_nestedtup _ =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in fst (snd x)" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_nestedtup2 _ =
  let prog = "let x = (flip 0.1, (flip 0.4, flip 0.7)) in ! fst (snd x)" in
  assert_feq 0.6 (parse_and_prob prog);
  assert_feq 0.6 (parse_optimize_and_prob prog)

let test_ite1 _ =
  let prog = "if flip 0.4 then true else false" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_ite2 _ =
  let prog = "if flip 0.4 then flip 0.6 else false" in
  assert_feq 0.24 (parse_and_prob prog);
  assert_feq 0.24 (parse_optimize_and_prob prog)

let test_ite3 _ =
  let prog = "if flip 0.4 then let z = observe false in flip 0.6 else false" in
  assert_feq 0.0 (parse_and_prob prog);
  assert_feq 0.0 (parse_optimize_and_prob prog)

let test_int1 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in x == int(2, 1)" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_int2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 0)) in x == int(2, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog);
  assert_feq (0.4 /. 0.9) (parse_optimize_and_prob prog)

let test_int3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 0) || x == int(2,1)) in x == int(2, 2)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_int4 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) in let z = observe ! (x == int(2, 1)) in x == int(2, 2)" in
  assert_feq (0.5 /. 0.6) (parse_and_prob prog);
  assert_feq (0.5 /. 0.6) (parse_optimize_and_prob prog)

let test_add1 _ =
  let prog = "let x = int(3, 0) + int(3, 1) in x == int(3, 1)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_add2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + int(2, 1) in x == int(2, 1)" in
  assert_feq 0.1 (parse_and_prob prog);
  assert_feq 0.1 (parse_optimize_and_prob prog)

let test_add3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) + discrete(1.0, 0.0, 0.0) in x == int(2, 1)" in
  assert_feq 0.4 (parse_and_prob prog);
  assert_feq 0.4 (parse_optimize_and_prob prog)

let test_add4 _ =
  let prog = "let x = discrete(0.25, 0.25, 0.25, 0.25) + discrete(0.25, 0.25, 0.25, 0.25) in x == int(2, 1)" in
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)

let test_add5 _ =
  let prog = "
   let x = discrete(0.3, 0.1, 0.2, 0.2, 0.2) in
   let y = discrete(0.1, 0.3, 0.2, 0.2, 0.2) in
   let sum = x + y in
   let z = observe x == int(3, 1) in
   sum == int(3, 1)" in
  assert_feq 0.1 (parse_and_prob prog);
  assert_feq 0.1 (parse_optimize_and_prob prog)

let test_add6 _ =
  let prog = "let x = discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125)
+ discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125) in x == int(3, 1)" in
  assert_feq 0.125 (parse_and_prob prog);
  assert_feq 0.125 (parse_optimize_and_prob prog)

let test_sub1 _ =
  let prog = "let x = int(3, 0) - int(3, 1) in x == int(3, 7)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_sub2 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) - int(2, 1) in x == int(2, 1)" in
  assert_feq 0.5 (parse_and_prob prog);
  assert_feq 0.5 (parse_optimize_and_prob prog)

let test_sub3 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5) - discrete(0.0, 1.0, 0.0) in x == int(2, 1)" in
  assert_feq 0.5 (parse_and_prob prog);
  assert_feq 0.5 (parse_optimize_and_prob prog)

let test_sub4 _ =
  let prog = "let x = discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125)
- discrete(0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125, 0.125) in x == int(3, 1)" in
  assert_feq 0.125 (parse_and_prob prog);
  assert_feq 0.125 (parse_optimize_and_prob prog)

let test_op1 _ =
  (*let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   x < y" in*)
  let prog = "
   discrete(0.1, 0.2, 0.3, 0.4) < discrete(0.4, 0.3, 0.2, 0.1)" in

  assert_feq (3.0 /. 20.0) (parse_and_prob prog);
  assert_feq (3.0 /. 20.0) (parse_optimize_and_prob prog)

let test_op2 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   x <= y" in
  assert_feq (7.0 /. 20.0) (parse_and_prob prog);
  assert_feq (7.0 /. 20.0) (parse_optimize_and_prob prog)

let test_op3 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   (x + y) < int(2, 2)" in
  assert_feq (23.0 /. 50.0) (parse_and_prob prog);
  assert_feq (23.0 /. 50.0) (parse_optimize_and_prob prog)

let test_op4 _ =
  let prog = "
   let x = discrete(0.1, 0.2, 0.3, 0.4) in
   let y = discrete(0.4, 0.3, 0.2, 0.1) in
   let tmp = observe (x + y) < int(2, 2) in
   x == y" in
  assert_feq (5.0 /. 23.0) (parse_and_prob prog);
  assert_feq (5.0 /. 23.0) (parse_optimize_and_prob prog)


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
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mul2 _ =
  let prog = "let x = int(3, 2) * int(3, 2) in x == int(3, 4)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mul3 _ =
  let prog = "let x = int(3, 3) * int(3, 3) in x == int(3, 1)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mul4 _ =
  let prog = "let x = int(4, 3) * int(4, 3) in x == int(4, 9)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mul5 _ =
  let prog = "let x = int(4, 3) * int(4, 3) * int(4, 3) in x == int(4, 11)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mul6 _ =
  let prog = "let x = discrete(0.1, 0.4, 0.5, 0.0) * int(2, 2) in x == int(2, 0)" in
  assert_feq 0.6 (parse_and_prob prog);
  assert_feq 0.6 (parse_optimize_and_prob prog)

let test_leftshift_1 _ =
  let prog = "let x = int(4, 1) in let y = x << 2 in y == int(4, 4)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_leftshift_2 _ =
  let prog = "let x = int(4, 1) in let y = x << 5 in y == int(4, 0)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_rightshift_1 _ =
  let prog = "let x = int(4, 8) in let y = x >> 2 in y == int(4, 2)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_rightshift_2 _ =
  let prog = "let x = int(4, 12) in let y = x >> 1 in y == int(4, 6)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_rightshift_3 _ =
  let prog = "let x = int(4, 12) in let y = x >> 5 in y == int(4, 0)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_rightshift_4 _ =
  let prog = "let x = int(2, 2) in int(2, 1) == (x >> 1)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_rightshift_5 _ =
  let prog = "
let a = int(2,2) in
let _x1 = if ( nth_bit(int(2,1), a)) then true else false in
let _x0 = if ( nth_bit(int(2,0), a)) then _x1 else true in
let b = a in
let _y1 = if ( nth_bit(int(2,1), b)) then true else false in
let _y0 = if ( nth_bit(int(2,1), b >> 1)) then _y1 else true in
_x0 <=> _y0" in
  assert_feq 1.0 (parse_and_prob prog)


let test_unif_1 _ =
  let prog1 = "let u = uniform(4, 0, 10) in u < int(4, 4)" in
  let prog2 = "let d = discrete(0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1) in d < int(4, 4)" in
  assert_feq (parse_and_prob prog1) (parse_and_prob prog2);
  assert_feq 0.4 (parse_and_prob prog1)

let test_unif_2 _ =
  let prog1 = "let u = uniform(3, 2, 6) in u == int(3, 0)" in
  let prog2 = "let d = discrete(0., 0., 0.25, 0.25, 0.25, 0.25) in d == int(3, 0)" in
  assert_feq (parse_and_prob prog1) (parse_and_prob prog2);
  assert_feq 0. (parse_and_prob prog1)

let test_unif_3 _ =
  let prog1 = "let u = uniform(3, 3, 4) in u == int(3, 3)" in
  let prog2 = "let d = discrete(0., 0., 0., 1., 0.) in d == int(3, 3)" in
  assert_feq (parse_and_prob prog1) (parse_and_prob prog2);
  assert_feq 1. (parse_and_prob prog1)

let test_unif_4 _ =
  let prog = "
    let u = uniform(2, 1, 4) in
    let d = discrete(0., 0.5, 0.25, 0.25) in
    u == d && u < int(2, 3)" in
  assert_feq 0.25 (parse_and_prob prog)


let test_binom_1 _ =
  let prog = "let b = binomial(3, 4, 0.25) in b == int(3, 1)" in
  assert_feq 0.421875 (parse_and_prob prog)

let test_binom_2 _ =
  let prog = "let b = binomial(5, 29, 0.5) in b <= int(5, 14)" in
  assert_feq 0.5 (parse_and_prob prog)

let test_binom_3 _ =
  let prog = "let b = binomial(3, 0, 0.5) in b == int(3, 0)" in
  assert_feq 1. (parse_and_prob prog)

let test_binom_4 _ =
  let prog = "let b = binomial(3, 1, 0.3) in b == int(3, 1)" in
  assert_feq 0.3 (parse_and_prob prog)


let test_fcall1 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(true) && foo(true)" in
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)

let test_fcall2 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(true) && foo(false)" in
  assert_feq 0.0 (parse_and_prob prog);
  assert_feq 0.0 (parse_optimize_and_prob prog)

let test_fcall3 _ =
  let prog = "
    fun foo(test: bool) {
      (flip 0.5) && test
    }
    foo(flip 0.5) && foo(flip 0.5)" in
  assert_feq 0.06250 (parse_and_prob prog);
  assert_feq 0.06250 (parse_optimize_and_prob prog)

let test_fcall4 _ =
  let prog = "
    fun foo(test: bool) {
      let tmp = observe test in
      true
    }
    let z = flip 0.5 in
    let tmp = foo(z) in
    z" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

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
  assert_feq (0.4 /. 0.46) (parse_and_prob prog);
  assert_feq (0.4 /. 0.46) (parse_optimize_and_prob prog)

let test_fcall6 _ =
  let prog = "
    fun foo(test1: (bool, bool)) {
      let k = observe (fst test1) || (snd test1) in
      false
    }
    let f1 = flip 0.4 in
    let tmp = foo((f1, flip 0.1)) in f1" in
  assert_feq (0.4 /. 0.46) (parse_and_prob prog);
  assert_feq (0.4 /. 0.46) (parse_optimize_and_prob prog)

let test_fcall7 _ =
  let prog = "
    fun foo(test1: int(2)) {
      let k = observe !(test1 == int(2, 0)) in
      false
    }
    let f1 = discrete(0.1, 0.4, 0.5) in
    let tmp = foo(f1) in f1 == int(2, 1)" in
  assert_feq (0.4 /. 0.9) (parse_and_prob prog);
  assert_feq (0.4 /. 0.9) (parse_optimize_and_prob prog)

let test_nthbit1 _ =
  let prog = "
    let f1 = discrete(0.1, 0.4, 0.3, 0.2) in
    nth_bit(int(2, 1), f1)" in
  assert_feq 0.6 (parse_and_prob prog)

let test_nthbit2 _ =
  let prog = "
    let f1 = discrete(0.1, 0.4, 0.3, 0.2) in
    nth_bit(int(2, 0), f1)" in
  assert_feq 0.5 (parse_and_prob prog)

let test_nthbit3 _ =
  let prog = "
    let a = int(2, 1) in nth_bit(int(2,1), a)" in
  assert_feq 1.0 (parse_and_prob prog)

let test_nthbit4 _ =
  let prog = "
    let a = int(2, 1) in nth_bit(int(2,0), a)" in
  assert_feq 0.0 (parse_and_prob prog)


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
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)

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
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)


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
  assert_feq 0.284172 (parse_and_prob prog);
  assert_feq 0.284172 (parse_optimize_and_prob prog)

let test_alarm _ =
  let prog = In_channel.read_all "../benchmarks/baselines/alarm.dice" in
  assert_feq (2969983.0 /. 992160802.0) (parse_and_prob prog);
  assert_feq (2969983.0 /. 992160802.0) (parse_optimize_and_prob prog)

let test_murder _ =
  let prog = In_channel.read_all "../benchmarks/baselines/murderMystery.dice" in
  assert_feq (9.0 /. 569.0) (parse_and_prob prog);
  assert_feq (9.0 /. 569.0) (parse_optimize_and_prob prog)

let test_evidence1 _ =
  let prog = In_channel.read_all "../benchmarks/baselines/evidence1.dice" in
  assert_feq (1.0 /. 3.0) (parse_and_prob prog);
  assert_feq (1.0 /. 3.0) (parse_optimize_and_prob prog)

let test_evidence2 _ =
  let prog = In_channel.read_all "../benchmarks/baselines/evidence2.dice" in
  assert_feq (2.0 /. 3.0) (parse_and_prob prog);
  assert_feq (2.0 /. 3.0) (parse_optimize_and_prob prog)

let test_grass _ =
  let prog = In_channel.read_all "../benchmarks/baselines/grass.dice" in
  assert_feq (509.0 /. 719.0) (parse_and_prob prog);
  assert_feq (509.0 /. 719.0) (parse_optimize_and_prob prog)

let test_cancer _ =
  let prog = In_channel.read_all "../resources/cancer_test.dice" in
  assert_feq (42709.0 /. 200000.0) (parse_and_prob prog);
  assert_feq (42709.0 /. 200000.0) (parse_optimize_and_prob prog)

let test_caesar_2 _ =
  let prog = In_channel.read_all "../resources/caesar_test.dice" in
  assert_feq  (1113032.0 /. 315312455.0) (parse_and_prob prog);
  assert_feq  (1113032.0 /. 315312455.0) (parse_optimize_and_prob prog)

let test_alarm_2 _ =
  (* the correct answer here is from ace *)
  let prog = In_channel.read_all "../resources/alarm_test.dice" in
  assert_feq 0.281037656 (parse_and_prob prog);
  assert_feq 0.281037656 (parse_optimize_and_prob prog)

let test_pmc1 _ =
  let prog = In_channel.read_all "../resources/pmc1.dice" in
  assert_feq (1023.0 /. 2048.0) (parse_and_prob prog);
  assert_feq (1023.0 /. 2048.0) (parse_optimize_and_prob prog)

let test_pmc2 _ =
  let prog = In_channel.read_all "../resources/pmc2.dice" in
  assert_feq (31.0 /. 64.0) (parse_and_prob prog);
  assert_feq (31.0 /. 64.0) (parse_optimize_and_prob prog)

let test_double_flip _ =
  let prog = "
    let c1 = flip 0.5 in
    let c2 = flip 0.5 in
    c1 && c2
    " in
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)

let test_typecheck_1 _ =
  let prog = "
    let c1 = discrete(0.1, 0.4, 0.5) in
    let c2 = int(2, 1) in
    (c1 == c2) || (c1 != c2)
    " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_mod_sub _ =
  let prog = "
    let c1 = int(3, 0) in
    let c2 = int(3, 1) in
    (c1 - c2) == int(3, 2)" in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

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
" in assert_feq 0.45 (parse_and_prob prog);
  assert_feq 0.45 (parse_optimize_and_prob prog)

let test_recursion _ =
  let prog = In_channel.read_all "../resources/recursion.dice" in
  assert_feq (0.5 ** 3.) (parse_and_prob prog);
  assert_feq (0.5 ** 3.) (parse_optimize_and_prob prog)

let test_caesar_recursive _ =
  let prog = "
    fun sendchar(key: int(2), observation: int(2)) {
      let gen = discrete(0.5, 0.25, 0.125, 0.125) in
      let enc = key + gen in
      observe observation == enc
    }
    fun loop(key: int(2), observation: int(2)): bool {
      let tmp = sendchar(key, observation) in
      if observation == int(2, 3)
        then true
        else loop(key, observation + int(2, 1))
    }
    let key = discrete(0.25, 0.25, 0.25, 0.25) in
    let tmp = loop(key, int(2, 0)) in
    key == int(2, 0)
  " in
  assert_feq 0.25 (parse_and_prob prog);
  assert_feq 0.25 (parse_optimize_and_prob prog)

let test_factorial _ =
  let prog = "
    fun fac(n: int(7)): int(7) {
      if n == int(7, 0) then int(7, 1) else n * fac(n - int(7, 1))
    }
    fac(int(7, 5)) == int(7, 120)
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_fibonacci _ =
  let prog = "
    fun fib(n: int(7)): int(7) {
      if n < int(7, 2) then n else fib(n - int(7, 1)) + fib(n - int(7, 2))
    }
    fib(int(7, 11)) == int(7, 89)
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_list _ =
  let prog = "
    let xs = [true, false, false] in
    (head xs) && !(head (tail xs)) && !(head (tail (tail xs)))
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_length _ =
  let prog = "
    let xs = [true, false, false] in
    (length xs) == int(4, 3)
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_empty _ =
  let prog = "
    let xs = [] : list(bool) in
    (length xs) == int(4, 0)
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_list_recursion _ =
  let prog = "
    fun index(n: int(2), xs: list(bool)): bool {
      if n == int(2, 0) then
        head xs
      else
        index(n - int(2, 1), tail xs)
    }
    let xs = [true, false, false] in
    !index(int(2, 2), xs) && !index(int(2, 1), xs) && index(int(2, 0), xs)
  " in
  assert_feq 1.0 (parse_and_prob prog);
  assert_feq 1.0 (parse_optimize_and_prob prog)

let test_list_distribution _ =
  let prog = "
    fun build(n: int(2)): list(bool) {
      if n == int(2, 0) then
        ([] : list(bool))
      else if flip 0.5 then
        flip 0.2 :: build(n - int(2, 1))
      else
        build(n - int(2, 1))
    }
    let xs = build(int(2, 3)) in
    " in
  let test prob expr =
    assert_feq prob (parse_and_prob (prog ^ expr));
    assert_feq prob (parse_optimize_and_prob (prog ^ expr)) in
  test (0.5 *. 0.5 *. 0.5) "(length xs) == int(4, 0)";
  test (0.5 *. 0.2 *. 0.5 *. 0.5 *. 3.) "if (length xs) == int(4, 1) then (head xs) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.5 *. 3.) "if (length xs) == int(4, 1) then !(head xs) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.2 *. 0.5 *. 3.) "if (length xs) == int(4, 2) then (head xs) && (head (tail xs)) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.8 *. 0.5 *. 3.) "if (length xs) == int(4, 2) then (head xs) && !(head (tail xs)) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.2 *. 0.5 *. 3.) "if (length xs) == int(4, 2) then !(head xs) && (head (tail xs)) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.8 *. 0.5 *. 3.) "if (length xs) == int(4, 2) then !(head xs) && !(head (tail xs)) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.2 *. 0.5 *. 0.2) "if (length xs) == int(4, 3) then (head xs) && (head (tail xs)) && (head (tail (tail xs))) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.2 *. 0.5 *. 0.8) "if (length xs) == int(4, 3) then (head xs) && (head (tail xs)) && !(head (tail (tail xs))) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.8 *. 0.5 *. 0.2) "if (length xs) == int(4, 3) then (head xs) && !(head (tail xs)) && (head (tail (tail xs))) else false";
  test (0.5 *. 0.2 *. 0.5 *. 0.8 *. 0.5 *. 0.8) "if (length xs) == int(4, 3) then (head xs) && !(head (tail xs)) && !(head (tail (tail xs))) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.2 *. 0.5 *. 0.2) "if (length xs) == int(4, 3) then !(head xs) && (head (tail xs)) && (head (tail (tail xs))) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.2 *. 0.5 *. 0.8) "if (length xs) == int(4, 3) then !(head xs) && (head (tail xs)) && !(head (tail (tail xs))) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.8 *. 0.5 *. 0.2) "if (length xs) == int(4, 3) then !(head xs) && !(head (tail xs)) && (head (tail (tail xs))) else false";
  test (0.5 *. 0.8 *. 0.5 *. 0.8 *. 0.5 *. 0.8) "if (length xs) == int(4, 3) then !(head xs) && !(head (tail xs)) && !(head (tail (tail xs))) else false"

let test_list_ex _ =
  let prog = "
    let xs = [flip 0.2, flip 0.4] in
    let ys = if flip 0.5 then (head xs) :: xs else tail xs in
    head ys
  " in
  assert_feq (0.2 *. 0.5 +. 0.4 *. 0.5) (parse_and_prob prog);
  assert_feq (0.2 *. 0.5 +. 0.4 *. 0.5) (parse_optimize_and_prob prog)

let test_lte_name _ =
  let prog1 = "uniform(3, 0, 8) <= uniform(3, 0, 8)" in
  let prog2 = "
    let a = uniform(3, 0, 8) in
    let b = uniform(3, 0, 8) in
    a <= b" in
  assert_feq (parse_and_prob prog1) (parse_and_prob prog2)

let test_lt_name _ =
  let prog1 = "uniform(3, 0, 8) < uniform(3, 0, 8)" in
  let prog2 = "
    let a = uniform(3, 0, 8) in
    let b = uniform(3, 0, 8) in
    a < b" in
  assert_feq (parse_and_prob prog1) (parse_and_prob prog2)


let test_bdd _ =
  let mgr = Bdd.mk_bdd_manager_default_order 100 in
  let v1 = Bdd.bdd_newvar mgr true in
  let v2 = Bdd.bdd_newvar mgr true in
  let v3 = Bdd.bdd_newvar mgr true in
  let and2 = Bdd.bdd_and mgr v1 v2 in
  let and3 = Bdd.bdd_and mgr (Bdd.bdd_and mgr v1 v2) v3 in
  let and3q = Bdd.bdd_exists mgr and3 (Bdd.bdd_topvar mgr v3) in
  assert_bool "testing eq" (Bdd.bdd_eq mgr and3q and2)
  (* assert_equal sz (Unsigned.UInt64.of_int 3) *)

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

  "test_leftshift_1">::test_leftshift_1;
  "test_leftshift_2">::test_leftshift_2;

  "test_rightshift_1">::test_rightshift_1;
  "test_rightshift_2">::test_rightshift_2;
  "test_rightshift_3">::test_rightshift_3;
  "test_rightshift_4">::test_rightshift_4;
  "test_rightshift_5">::test_rightshift_5;

  "test_unif_1">::test_unif_1;
  "test_unif_2">::test_unif_2;
  "test_unif_3">::test_unif_3;
  "test_unif_4">::test_unif_4;

  (*"test_binom_1">::test_binom_1;
  "test_binom_2">::test_binom_2;
  "test_binom_3">::test_binom_3;
  "test_binom_4">::test_binom_4;*)

  "test_fcall1">::test_fcall1;
  "test_fcall2">::test_fcall2;
  "test_fcall3">::test_fcall3;
  "test_fcall4">::test_fcall4;
  "test_fcall5">::test_fcall5;
  "test_fcall6">::test_fcall6;
  "test_fcall7">::test_fcall7;

  "test_nthbit1">::test_nthbit1;
  "test_nthbit2">::test_nthbit2;
  "test_nthbit3">::test_nthbit3;
  "test_nthbit4">::test_nthbit4;

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
  (* "test_pmc1">::test_pmc1;
   * "test_pmc2">::test_pmc2; *)

  "test_recursion">::test_recursion;
  "test_caesar_recursive">::test_caesar_recursive;
  "test_factorial">::test_factorial;
  "test_fibonacci">::test_fibonacci;

  "test_list">::test_list;
  "test_length">::test_length;
  "test_empty">::test_empty;
  "test_list_recursion">::test_list_recursion;
  (* "test_list_distribution">::test_list_distribution; *)
  "test_list_ex">::test_list_ex;
  "test_bdd">::test_bdd;
  "test_lte_name">::test_lte_name;
  "test_lt_name">::test_lt_name;
]

let () =
  run_test_tt_main expression_tests;
