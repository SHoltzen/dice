(** Passes over the external and internal grammar.
  * Implementations of syntactic sugar, optimizations, etc. *)

(** Inline all function calls *)
val inline_functions : ExternalGrammar.program -> ExternalGrammar.program

(** Compute the number of paths through the probabilistic program.
  * Note: assumes that function calls are inlined, no iteration *)
val num_paths : ExternalGrammar.program -> LogProbability.t

val from_external_expr : ExternalGrammar.eexpr -> CoreGrammar.expr
val from_external_func : ExternalGrammar.func -> CoreGrammar.func
val from_external_prog: ExternalGrammar.program -> CoreGrammar.program
