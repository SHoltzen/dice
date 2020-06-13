open VarState
open Cudd
open Core
open Wmc

(** Result of compiling an expression *)
type compiled_expr = {
  state: varstate btree;
  z: Bdd.dt;
  flips: Bdd.dt List.t}

type compiled_func = {
  args: (varstate btree) List.t;
  body: compiled_expr;
}

type compile_context = {
  man: Man.dt;
  name_map: (int, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
  lazy_eval: bool; (* true if lazy let evaluation *)
  funcs: (String.t, compiled_func) Hashtbl.Poly.t;
}

type compiled_program = {
  ctx: compile_context;
  body: compiled_expr;
}

(** Compile the input program to a [compiled_program] *)
val compile_program: CoreGrammar.program -> compiled_program

val get_prob: CoreGrammar.program -> float
