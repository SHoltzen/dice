type t

val mult : t -> t -> t
val conv: t -> float
val add : t -> t -> t
val div : t -> t -> t
val to_dec : t -> float
val make : float -> t
val rat_div_and_conv : Bignum.t -> Bignum.t -> Bignum.t

(** prints the logarithm in the chosen base *)
val to_string : float -> t -> string
