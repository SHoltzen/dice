(** Defines the logical formula interface in dice grammar *)

type expr =
  | And of expr * expr
  | Or of expr * expr
  | Atom of String.t
  | True
  | Tup of expr * expr
  | Neg of expr
[@@deriving sexp_of]

type weights = (String.t, Bignum.t) Core.Hashtbl.Poly.t 
[@@deriving sexp_of]

type program = {
  body: expr;
  weights: weights;
}
[@@deriving sexp_of]

type literal = 
  | Pos of String.t
  | Neg of String.t
[@@deriving sexp_of]

type cnf = literal List.t List.t
[@@deriving sexp_of]

type label = 
  [ `False 
  | `Int of int 
  | `True 
  | `Tup of label * label 
  | `List of label List.t]

type wcnf = {
  table: (label * cnf) List.t;
  weights: weights;
}

val string_of_expr : expr -> String.t
val string_of_prog : program -> String.t

val string_of_cnf : cnf -> String.t
val string_of_wcnf : wcnf -> String.t

val extract_tup : expr -> expr