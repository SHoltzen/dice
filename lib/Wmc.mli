
type weight = (int, (Bignum.t*Bignum.t)) Core.Hashtbl.Poly.t

(** Performs a weighted model count of the BDD with the supplied weight function. *)
val wmc : ?float_wmc:bool -> Cudd.Bdd.dt -> weight -> Bignum.t
