(** Miscellaneous utilities *)

(** Checks if two floats are approximately equal. Raises an exception if they are not. *)
val assert_feq: float -> float -> unit

(** [parse_and_prob]: [debug flag] -> [program text] -> [prob]
    Parses and prints the probability of [program text]. *)
val parse_and_prob: ?debug:bool -> string -> float


(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
  *)
val dir_contents: string -> string List.t

exception Syntax_error of string

(** [parse_with_error] parses [lexbuf] as a program or fails with a syntax error *)
val parse_with_error: Lexing.lexbuf -> ExternalGrammar.program

(** prints the current position of the lex buffer to the out channel *)
val print_position : out_channel -> Lexing.lexbuf -> unit
