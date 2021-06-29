(** Miscellaneous utilities *)

(** Checks if two floats are approximately equal. Raises an exception if they are not. *)
val assert_feq: float -> float -> unit

(** [dir_contents] returns the paths of all regular files that are
 * contained in [dir]. Each file is a path starting with [dir].
  *)
val dir_contents: string -> string List.t

val log2 : float -> float

val bit_length : int -> int

(** true if the two arguments are very close to each other (TODO avoid using this with rationals )*)
val within_epsilon : float -> float -> bool
