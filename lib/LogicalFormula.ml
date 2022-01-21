open Core

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

type dddnf = literal List.t List.t
[@@deriving sexp_of]

let string_of_expr e =
  Sexp.to_string_hum (sexp_of_expr e)

let string_of_prog p =
  (* let e = p.body in
  let r = Hashtbl.fold (fun x y -> Printf.printf "%s -> %s\n" x y) ht;;
  string_of_expr e *)
  Sexp.to_string_hum (sexp_of_program p)

let string_of_cnf e =
  Sexp.to_string_hum (sexp_of_cnf e)

let string_of_dddnf e =
  Sexp.to_string_hum (sexp_of_dddnf e)