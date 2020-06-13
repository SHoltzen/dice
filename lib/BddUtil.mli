(** Utilities for working with BDDs. *)

type name_map = (int, String.t) Core.Hashtbl.Poly.t

(** Dumps to stdout a dotfile that describes the BDD. *)
val dump_dot : name_map -> Cudd.Bdd.dt -> unit
