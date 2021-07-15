
type weight = (int, (float*float)) Core.Hashtbl.Poly.t

(** Performs a weighted model count of the BDD with the supplied weight function. *)
val wmc : Bdd.bddptr -> weight -> float
