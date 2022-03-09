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

let extract_tup (e: expr ref) (b: binary ref) : expr ref = 
  
  let rec extract_tup_e (e: expr ref) : expr ref = 
    match !e with
    | And(e1, e2) -> 
      let e1' = extract_tup_e e1 in
      let e2' = extract_tup_e e2 in
      (match !e1', !e2' with
      | Tup(e1_1, e1_2), Tup(e2_1, e2_2) ->
        (* not sure about this case *)
        let ref_and1 = Hashtbl.Poly.find_or_add !b (e1_1, e2_1, And_ind)
          ~default:(fun () -> ref (And(e1_1, e2_1))) in
        let ref_and2 = Hashtbl.Poly.find_or_add !b (e1_2, e2_2, And_ind)
          ~default:(fun () -> ref (And(e1_2, e2_2))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_and1, ref_and2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_and1, ref_and2))) in
        ref_tup
      | Tup(e1_1, e1_2), _ ->
        let ref_and1 = Hashtbl.Poly.find_or_add !b (e1_1, e2', And_ind)
          ~default:(fun () -> ref (And(e1_1, e2'))) in
        let ref_and2 = Hashtbl.Poly.find_or_add !b (e1_2, e2', And_ind)
          ~default:(fun () -> ref (And(e1_2, e2'))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_and1, ref_and2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_and1, ref_and2))) in
        ref_tup
      | _, Tup(e2_1, e2_2) ->
        let ref_and1 = Hashtbl.Poly.find_or_add !b (e1', e2_1, And_ind)
          ~default:(fun () -> ref (And(e1', e2_1))) in
        let ref_and2 = Hashtbl.Poly.find_or_add !b (e1', e2_2, And_ind)
          ~default:(fun () -> ref (And(e1', e2_2))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_and1, ref_and2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_and1, ref_and2))) in
        ref_tup
      | _ -> 
        let ref_and = Hashtbl.Poly.find_or_add !b (e1', e2', And_ind)
          ~default:(fun () -> ref (And(e1', e2'))) in
        ref_and)
    | Or(e1, e2) -> 
      let e1' = extract_tup_e e1 in
      let e2' = extract_tup_e e2 in
      (match !e1', !e2' with
      | Tup(e1_1, e1_2), Tup(e2_1, e2_2) ->
        (* not sure about this case *)
        let ref_or1 = Hashtbl.Poly.find_or_add !b (e1_1, e2_1, Or_ind)
          ~default:(fun () -> ref (Or(e1_1, e2_1))) in
        let ref_or2 = Hashtbl.Poly.find_or_add !b (e1_2, e2_2, Or_ind)
          ~default:(fun () -> ref (Or(e1_2, e2_2))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_or1, ref_or2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_or1, ref_or2))) in
        ref_tup
      | Tup(e1_1, e1_2), _ ->
        let ref_or1 = Hashtbl.Poly.find_or_add !b (e1_1, e2', Or_ind)
          ~default:(fun () -> ref (Or(e1_1, e2'))) in
        let ref_or2 = Hashtbl.Poly.find_or_add !b (e1_2, e2', Or_ind)
          ~default:(fun () -> ref (Or(e1_2, e2'))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_or1, ref_or2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_or1, ref_or2))) in
        ref_tup
      | _, Tup(e2_1, e2_2) ->
        let ref_or1 = Hashtbl.Poly.find_or_add !b (e1', e2_1, Or_ind)
          ~default:(fun () -> ref (Or(e1', e2_1))) in
        let ref_or2 = Hashtbl.Poly.find_or_add !b (e1', e2_2, Or_ind)
          ~default:(fun () -> ref (Or(e1', e2_2))) in
        let ref_tup = Hashtbl.Poly.find_or_add !b (ref_or1, ref_or2, Tup_ind)
          ~default:(fun () -> ref (Tup(ref_or1, ref_or2))) in
        ref_tup
      | _ -> 
        let ref_or = Hashtbl.Poly.find_or_add !b (e1', e2', Or_ind)
          ~default:(fun () -> ref (Or(e1', e2'))) in
        ref_or)
    | Atom(_) | True | Not(_) | Tup(_) -> e
  in
  extract_tup_e e

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
