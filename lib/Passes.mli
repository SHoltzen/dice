(** Passes over the external and internal grammar.
  * Implementations of syntactic sugar, optimizations, etc. *)

type config = { max_list_length: int }

val default_config : config

val expand_recursion : ?recursion_limit:int -> ExternalGrammar.program -> ExternalGrammar.program

(** Inline all function calls *)
val inline_functions : ExternalGrammar.program -> ExternalGrammar.program

(** Compute the number of paths through the probabilistic program.
  * Note: assumes that function calls are inlined, no iteration *)
val num_paths : ExternalGrammar.program -> LogProbability.t

val from_external_prog: ?cfg:config -> ExternalGrammar.program -> (ExternalGrammar.typ * CoreGrammar.program)

val from_external_prog_optimize: ?cfg:config -> ExternalGrammar.program -> bool -> bool -> bool -> (ExternalGrammar.typ * CoreGrammar.program)
