(** Passes over the external and internal grammar.
  * Implementations of syntactic sugar, optimizations, etc. *)

val expand_recursion : ExternalGrammar.program -> ExternalGrammar.program

(** Inline all function calls *)
val inline_functions : ExternalGrammar.program -> ExternalGrammar.program

(** Compute the number of paths through the probabilistic program.
  * Note: assumes that function calls are inlined, no iteration *)
val num_paths : ExternalGrammar.program -> LogProbability.t

val from_external_prog: ExternalGrammar.program -> (ExternalGrammar.typ * CoreGrammar.program)

val from_external_prog_optimize: ExternalGrammar.program -> bool -> bool -> bool -> (ExternalGrammar.typ * CoreGrammar.program)
