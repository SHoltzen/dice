
type weight = (Bdd.label, (Bignum.t*Bignum.t)) Core.Hashtbl.Poly.t

(** Performs a weighted model count of the BDD with the supplied weight function. *)
val wmc : wmc_type: int -> Bdd.manager -> Bdd.bddptr -> weight -> Bignum.t
