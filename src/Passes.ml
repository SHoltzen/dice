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
    | Plus(e1, e2) -> Plus(helper e1, helper e2)
    | Eq(e1, e2) -> Eq(helper e1, helper e2)
    | Neq(e1, e2) -> Neq(helper e1, helper e2)
    | Minus(e1, e2) -> Minus(helper e1, helper e2)
    | Mult(e1, e2) -> Mult(helper e1, helper e2)
    | Div(e1, e2) -> Div(helper e1, helper e2)
    | Lt(e1, e2) -> Lt(helper e1, helper e2)
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
      let inlined = helper cur_f.body in
      List.fold (List.zip_exn cur_f.args args) ~init:inlined ~f:(fun acc (arg, v) -> Let(fst arg, v, acc)) in
  {functions=[]; body=helper p.body}

let num_paths (p: ExternalGrammar.program) : LogProbability.t =
  let inlined = inline_functions p in
  let rec helper (e: ExternalGrammar.eexpr) =
    match e with
    | And(e1, e2)
    | Or(e1, e2)
    | Plus(e1, e2)
    | Eq(e1, e2)
    | Minus(e1, e2)
    | Neq(e1, e2)
    | Div(e1, e2)
    | Mult(e1, e2)
    | Lt(e1, e2)
    | Gt(e1, e2)
    | Lte(e1, e2)
    | Gte(e1, e2)
    | Tup(e1, e2)
    | Let(_, e1, e2)->
      let s1 = helper e1 in
      let s2 = helper e2 in LogProbability.mult s1 s2
    | Not(e) -> helper e
    | Flip(f) -> LogProbability.make 2.0
    | Ident(s) ->  LogProbability.make 1.0
    | Discrete(l) -> LogProbability.make (float_of_int (List.length l))
    | Int(sz, v) -> LogProbability.make 1.0
    | True -> LogProbability.make 1.0
    | False -> LogProbability.make 1.0
    | Observe(e) -> helper e
    | Ite(g, thn, els) ->
      let gc = helper g in
      let tc = helper thn in
      let ec = helper els in
      LogProbability.mult gc (LogProbability.add tc ec)
    | Snd(e) | Fst(e) -> helper e
    | FuncCall(id, args) -> failwith "unreachable, functions inlined" in
  helper inlined.body
