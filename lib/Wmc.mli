
type weight = (Bdd.label, (float*float)) Core.Hashtbl.Poly.t

(** Performs a weighted model count of the BDD with the supplied weight function. *)
val wmc : Bdd.manager -> Bdd.bddptr -> weight -> float
