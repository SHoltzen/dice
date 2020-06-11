type t

val mult : t -> t -> t
val add : t -> t -> t
val div : t -> t -> t
val to_dec : t -> float
val make : float -> t
(** prints the logarithm in the chosen base *)
val to_string : float -> t -> string
