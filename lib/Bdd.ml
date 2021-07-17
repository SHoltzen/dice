open Foreign
open Ctypes
open PosixTypes

let librsdd = Dl.dlopen ~flags:[Dl.RTLD_LAZY] ~filename:"/Users/sholtzen/Documents/Programming/rsdd/target/release/librsdd.dylib"

type manager = unit ptr
let manager : manager typ = ptr void

type bddptr = size_t
type label = size_t

let bddptr = size_t

let label = size_t

let mk_bdd_manager_default_order =
  foreign "rsdd_mk_bdd_manager_default_order" (Ctypes.int @-> returning manager)

let bdd_newvar =
  foreign "rsdd_new_var" (manager @-> bool @-> returning bddptr)

let bdd_and =
  foreign "rsdd_and" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_or =
  foreign "rsdd_or" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_iff =
  foreign "rsdd_iff" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_xor =
  foreign "rsdd_xor" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_ite =
  foreign "rsdd_ite" (manager @-> bddptr @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_negate =
  foreign "rsdd_negate" (manager @-> bddptr @-> returning bddptr)

let bdd_true =
  foreign "rsdd_true" (manager @-> returning bddptr)

let bdd_false =
  foreign "rsdd_false" (manager @-> returning bddptr)

let bdd_exists =
  foreign "rsdd_exists" (manager @-> bddptr @-> label @-> returning bddptr)

let bdd_condition =
    foreign "rsdd_condition" (manager @-> bddptr @-> label @-> bool @-> returning bddptr)

let bdd_low =
  foreign "rsdd_low" (manager @-> bddptr @-> returning bddptr)

let bdd_high =
  foreign "rsdd_high" (manager @-> bddptr @-> returning bddptr)

let bdd_compose =
  foreign "rsdd_compose" (manager @-> bddptr @-> label @-> bddptr @-> returning bddptr)

let bdd_is_true =
  foreign "rsdd_is_true" (manager @-> bddptr @-> returning bool)

let bdd_is_false=
  foreign "rsdd_is_false" (manager @-> bddptr @-> returning bool)

let bdd_size =
  foreign "rsdd_size" (manager @-> bddptr @-> returning uint64_t)

let bdd_topvar =
  foreign "rsdd_topvar" (manager @-> bddptr @-> returning label)

let bdd_is_var =
  foreign "rsdd_is_var" (manager @-> bddptr @-> returning bool)

let bdd_eq =
  foreign "rsdd_eq_bdd" (manager @-> bddptr @-> bddptr @-> returning bool)

let bdd_is_const mgr bdd = not (bdd_is_var mgr bdd)

let int_of_label (lbl : label) : int = Unsigned.Size_t.to_int lbl
