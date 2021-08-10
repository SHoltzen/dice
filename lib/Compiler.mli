open VarState
open Core
open Wmc

(** Result of compiling an expression *)
type compiled_expr = {
  state: Bdd.bddptr btree;
  z: Bdd.bddptr;
  flips: Bdd.bddptr List.t}

type compiled_func = {
  args: (Bdd.bddptr btree) List.t;
  body: compiled_expr;
}


type compile_context = {
  man: Bdd.manager;
  name_map: (Bdd.label, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
  eager_eval: bool; (* true if lazy let evaluation *)
  funcs: (String.t, compiled_func) Hashtbl.Poly.t;
}

type compiled_program = {
  ctx: compile_context;
  body: compiled_expr;
}

(** Compile the input program to a [compiled_program] *)
val compile_program: CoreGrammar.program -> eager_eval:bool -> compiled_program

val get_prob: CoreGrammar.program -> Bignum.t

exception Syntax_error of string

(** [parse_with_error] parses [lexbuf] as a program or fails with a syntax error *)
val parse_with_error: Lexing.lexbuf -> ExternalGrammar.program

(** [parse_and_prob]: [debug flag] -> [program text] -> [prob]
    Parses and prints the probability of [program text]. *)
val parse_and_prob: ?debug:bool -> string -> float

val parse_optimize_and_prob: ?debug:bool -> string -> float

(** prints the current position of the lex buffer to the out channel *)
val print_position : out_channel -> Lexing.lexbuf -> unit

