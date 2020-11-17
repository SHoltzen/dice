open Cudd
open Core

(** A simple generic btree datastructure. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

val map_tree: 'a btree -> ('a -> 'b) -> 'b btree
val iter_tree: 'a btree -> ('a -> unit) -> unit
val collect_leaves: 'a btree -> 'a List.t
val zip_tree : 'a btree -> 'b btree -> ('a * 'b) btree

val extract_leaf : 'a btree -> 'a

(** [get_table] gets a list of all possible instantiations of BDDs in [st]. *)
val get_table: Bdd.dt btree ->
  ExternalGrammar.typ ->
  (([> `False | `Int of int | `True | `Tup of 'a * 'a ] as 'a) *  Cudd.Man.d Cudd.Bdd.t) list

(** [state_size] computes the total number of unique nodes in the list of
    varstates [states] *)
val state_size: Bdd.dt btree Core.List.t -> int

(** [subst_state] : x -> state -> f -> bdd, substitutes the variable x for the state `state` in f *)
val subst_state : Bdd.dt btree -> Bdd.dt btree -> Bdd.dt btree -> Bdd.dt btree
