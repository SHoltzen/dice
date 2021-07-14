open Foreign
open Ctypes

let librsdd = Dl.dlopen ~flags:[Dl.RTLD_LAZY] ~filename:"/Users/sholtzen/Documents/Programming/rsdd/target/release/librsdd.dylib"

type manager = unit ptr
let manager : manager typ = ptr void

let bddptr = int

let label = int


let mk_bdd_manager_default_order =
  foreign "rsdd_mk_bdd_manager_default_order" (Ctypes.int @-> returning manager)

let bdd_newvar =
  foreign "rsdd_new_var" (manager @-> returning bddptr)

let bdd_and =
  foreign "rsdd_and" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_or =
  foreign "rsdd_or" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_iff =
  foreign "rsdd_iff" (manager @-> bddptr @-> bddptr @-> returning bddptr)

let bdd_true =
  foreign "rsdd_true" (manager @-> returning bddptr)

let bdd_false =
  foreign "rsdd_false" (manager @-> returning bddptr)

let bdd_exists =
  foreign "rsdd_exists" (manager @-> bddptr @-> int @-> returning bddptr)

let bdd_condition =
    foreign "rsdd_condition" (manager @-> bddptr @-> label @-> bool @-> returning bddptr)

let bdd_size =
  foreign "rsdd_size" (manager @-> bddptr @-> returning uint64_t)

let bdd_topvar =
  foreign "rsdd_topvar" (manager @-> bddptr @-> returning label)

let is_var =
  foreign "rsdd_is_var" (manager @-> bddptr @-> returning bool)

let bdd_eq =
  foreign "rsdd_eq_bdd" (manager @-> bddptr @-> bddptr @-> returning bool)

