(** Performs optimization passes over the core grammar **)

open Core
open ExternalGrammar

let inline_functions (p: ExternalGrammar.program) =
  let function_map = List.fold p.functions ~init:(Map.Poly.empty) ~f:(fun acc f ->
      Map.Poly.add_exn acc f.name f) in
  let rec helper (e: ExternalGrammar.eexpr) =
    match e with
    | And(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in And(s1, s2)
    | Or(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Or(s1, s2)
    | Plus(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Plus(s1, s2)
    | Eq(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Eq(s1, s2)
    | Neq(e1, e2) -> helper(Not(Eq(e1, e2)))
    | Minus(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Minus(s1, s2)
    | Mult(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Mult(s1, s2)
    | Div(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Div(s1, s2)
    | Lt(e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Lt(s1, s2)
    | Lte(e1, e2) -> helper(Or(Lt(e1, e2), Eq(e1, e2)))
    | Gt(e1, e2) -> helper(Not(Lte(e1, e2)))
    | Gte(e1, e2) -> helper(Not(Lt(e1, e2)))
    | Not(e) -> Not(helper e)
    | Flip(f) -> Flip(f)
    | Ident(s) -> Ident(s)
    | Discrete(l) -> Discrete(l)
    | Int(sz, v) -> Int(sz, v)
    | True -> True
    | False -> False
    | Observe(e) -> Observe(helper e)
    | Let(x, e1, e2) -> Let(x, helper e1, helper e2)
    | Ite(g, thn, els) -> Ite(helper g, helper thn, helper els)
    | Snd(e) -> Snd(helper e)
    | Fst(e) -> Fst(helper e)
    | Tup(e1, e2) -> Tup(helper e1, helper e2)
    | FuncCall(id, args) ->
      let cur_f = Map.Poly.find_exn function_map id in
      List.fold (List.zip_exn cur_f.args args) ~init:(cur_f.body) ~f:(fun acc (arg, v) -> Let(fst arg, v, acc)) in
  {functions=[]; body=helper p.body}
