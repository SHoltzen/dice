open VarState
open Cudd
open Core
open Wmc


type subst = (Bdd.dt * Bdd.dt) List.t

(** Result of compiling an expression *)
type compiled_expr = {
  state: Bdd.dt btree;
  z: Bdd.dt;
  subst: subst;
  flips: Bdd.dt List.t;
}

type compiled_func = {
  args: (Bdd.dt btree) List.t;
  body: compiled_expr;
  
  local_bools: int List.t;
  arg_bools: int List.t;
}


type compile_context = {
  man: Man.dt;
  name_map: (int, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
  funcs: (String.t, compiled_func) Hashtbl.Poly.t;
}

type compiled_program = {
  ctx: compile_context;
  body: compiled_expr;
}

(** Compile the input program to a [compiled_program] *)
val compile_program: CoreGrammar.program -> compiled_program

val get_prob: CoreGrammar.program -> float

exception Syntax_error of string

(** [parse_with_error] parses [lexbuf] as a program or fails with a syntax error *)
val parse_with_error: Lexing.lexbuf -> ExternalGrammar.program

(** [parse_and_prob]: [debug flag] -> [program text] -> [prob]
    Parses and prints the probability of [program text]. *)
val parse_and_prob: ?debug:bool -> string -> float

val parse_optimize_and_prob: ?debug:bool -> string -> float

(** prints the current position of the lex buffer to the out channel *)
val print_position : out_channel -> Lexing.lexbuf -> unit

