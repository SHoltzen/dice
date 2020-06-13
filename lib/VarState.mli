open Cudd
open Core

(** A simple generic btree datastructure. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

(** Holds the outcome of compiling an expression *)
type varstate =
    BddLeaf of Bdd.dt
  | IntLeaf of Bdd.dt List.t


val map_tree: 'a btree -> ('a -> 'b) -> 'b btree
val iter_tree: 'a btree -> ('a -> unit) -> unit
val map_bddtree : varstate btree -> (Bdd.dt -> Bdd.dt) -> varstate btree
val fold_bddtree: varstate btree -> 'a -> ('a -> Bdd.dt -> 'a) -> 'a
val zip_tree : 'a btree -> 'b btree -> ('a * 'b) btree


val extract_bdd: varstate btree -> Bdd.dt
val extract_discrete: varstate btree -> Bdd.dt List.t


(** [get_table] gets a list of all possible instantiations of BDDs in [st]. *)
val get_table: varstate btree -> (([> `False | `Int of int * int | `True | `Tup of 'a * 'a ] as 'a) *  Cudd.Man.d Cudd.Bdd.t) list


(** [state_size] computes the total number of unique nodes in the list of
    varstates [states] *)
val state_size: varstate btree Core.List.t -> int
