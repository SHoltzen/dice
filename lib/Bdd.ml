(* why is this here? For some reason, the static object file for rsdd is not
   linked in and recognizable by Ctypes unless you reference an external symbol
   *before* Ctypes is imported, so I reference a symbol here.

   You do not want to know how long it took me to resolve this.
*)
(* original source: https://github.com/ocamllabs/ocaml-ctypes/issues/541*)
external _force_link_ : unit -> unit = "rsdd_mk_bdd_manager_default_order"

open Core
open Foreign
open Ctypes
open PosixTypes

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

(** Compose vars into f according to bdds*)
let bdd_vector_compose man f (vars: label List.t) (bdds: bddptr List.t) =
  let zipped = List.zip_exn vars bdds in
  List.fold zipped ~init:f ~f:(fun acc (v, bdd) ->
      bdd_compose man acc v bdd
    )

 
let man_print_stats =
  foreign "rsdd_print_stats" (manager @-> returning void)

let bdd_num_recursive_calls = 
  foreign "rsdd_num_recursive_calls" (manager @-> returning uint64_t)

let bdd_is_const mgr bdd = not (bdd_is_var mgr bdd)

let int_of_label (lbl : label) : int = Unsigned.Size_t.to_int lbl

