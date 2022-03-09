(** Defines the logical formula interface in dice grammar *)

type expr =
  | And of expr ref * expr ref
  | Or of expr ref * expr ref
  | Atom of String.t
  | True
  | Tup of expr ref * expr ref
  | Not of expr ref
[@@deriving sexp_of]

type weights = (String.t, Bignum.t) Core.Hashtbl.Poly.t 
[@@deriving sexp_of]

type ind = 
  | And_ind
  | Or_ind
  | Tup_ind
[@@deriving sexp_of]

type binary = ((expr ref * expr ref * ind), expr ref) Core.Hashtbl.Poly.t
[@@deriving sexp_of]

type unary = (expr ref, expr ref) Core.Hashtbl.Poly.t
[@@deriving sexp_of]

type program = {
  body: expr ref;
  weights: weights;
  binary: binary ref;
  unary: unary ref;
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

val string_of_expr : expr ref -> String.t
val string_of_prog : program -> String.t

val string_of_cnf : cnf -> String.t
val string_of_wcnf : wcnf -> String.t

val extract_tup : expr ref -> binary ref -> expr ref

val size_of_lf : program -> int