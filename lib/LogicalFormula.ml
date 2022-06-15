open Core

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

let string_of_expr e =
  Sexp.to_string_hum (sexp_of_expr !e)

let string_of_prog p =
  (* let e = p.body in
  let r = Hashtbl.fold (fun x y -> Printf.printf "%s -> %s\n" x y) ht;;
  string_of_expr e *)
  Sexp.to_string_hum (sexp_of_program p)

let string_of_cnf e =
  Sexp.to_string_hum (sexp_of_cnf e)

let string_of_wcnf wcnf =
  let tbl = List.fold wcnf.table ~init:"" ~f:(fun acc (_, c) -> 
    Format.sprintf "%s\n\n%s" acc (string_of_cnf c))
  in
  let w = Sexp.to_string_hum (sexp_of_weights wcnf.weights) in
  Format.sprintf "%s\n%s" tbl w

let size_of_lf (p: program) : int =
  let rec size (e: expr ref) (acc: int) : int =
    match !e with
    | And(e1, e2) | Or(e1, e2) | Tup(e1, e2) -> 
      let s1 = size e1 acc in
      size e2 (s1+1)
    | Not(e1) ->
      size e1 (acc+1)
    | Atom(_) | True -> acc+1
  in
  size p.body 0
