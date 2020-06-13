(** Performs optimization passes over the core grammar **)

open Core
open ExternalGrammar

let inline_functions (p: ExternalGrammar.program) =
  let function_map = List.fold p.functions ~init:(Map.Poly.empty) ~f:(fun acc f ->
      Map.Poly.add_exn acc ~key:f.name ~data:f) in
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
    | Iter(f, init, k) ->
      List.fold (List.init k ~f:(fun _ -> ())) ~init:init
        ~f:(fun acc _ -> FuncCall(f, [acc]))
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
    | Flip(_) -> LogProbability.make 2.0
    | Ident(_) ->  LogProbability.make 1.0
    | Discrete(l) -> LogProbability.make (float_of_int (List.length l))
    | Int(_, _) -> LogProbability.make 1.0
    | True -> LogProbability.make 1.0
    | False -> LogProbability.make 1.0
    | Observe(e) -> helper e
    | Ite(g, thn, els) ->
      let gc = helper g in
      let tc = helper thn in
      let ec = helper els in
      LogProbability.mult gc (LogProbability.add tc ec)
    | Snd(e) | Fst(e) -> helper e
    | _ -> failwith "unreachable, functions inlined" in
  helper inlined.body

let rec from_external_expr (e: ExternalGrammar.eexpr) : CoreGrammar.expr =
  match e with
  | And(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in And(s1, s2)
  | Or(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Or(s1, s2)
  | Plus(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Plus(s1, s2)
  | Eq(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Eq(s1, s2)
  | Neq(e1, e2) -> from_external_expr(Not(Eq(e1, e2)))
  | Minus(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Minus(s1, s2)
  | Mult(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Mult(s1, s2)
  | Div(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Div(s1, s2)
  | Lt(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Lt(s1, s2)
  | Lte(e1, e2) -> from_external_expr(Or(Lt(e1, e2), Eq(e1, e2)))
  | Gt(e1, e2) -> from_external_expr(Not(Lte(e1, e2)))
  | Gte(e1, e2) -> from_external_expr(Not(Lt(e1, e2)))
  | Not(e) -> Not(from_external_expr e)
  | Flip(f) -> Flip(f)
  | Ident(s) -> Ident(s)
  | Discrete(l) -> Discrete(l)
  | Int(sz, v) -> Int(sz, v)
  | True -> True
  | False -> False
  | Observe(e) -> Observe(from_external_expr e)
  | Let(x, e1, e2) -> Let(x, from_external_expr e1, from_external_expr e2)
  | Ite(g, thn, els) -> Ite(from_external_expr g, from_external_expr thn, from_external_expr els)
  | Snd(e) -> Snd(from_external_expr e)
  | Fst(e) -> Fst(from_external_expr e)
  | Tup(e1, e2) -> Tup(from_external_expr e1, from_external_expr e2)
  | FuncCall(id, args) -> FuncCall(id, List.map args ~f:(fun i -> from_external_expr i))
  | Iter(f, init, k) ->
    let e = from_external_expr init in
    List.fold (List.init k ~f:(fun _ -> ()))  ~init:e
      ~f:(fun acc _ -> FuncCall(f, [acc]))

let rec from_external_typ (t:ExternalGrammar.typ) : CoreGrammar.typ =
  match t with
    TBool -> TBool
  | TInt(sz) -> TInt(sz)
  | TTuple(t1, t2) -> TTuple(from_external_typ t1, from_external_typ t2)

let from_external_arg (a:ExternalGrammar.arg) : CoreGrammar.arg =
  let (name, t) = a in
  (name, from_external_typ t)

let from_external_func (f: ExternalGrammar.func) : CoreGrammar.func =
  {name = f.name;
   args = List.map f.args ~f:from_external_arg;
   body = from_external_expr f.body}

let from_external_prog (p: ExternalGrammar.program) : CoreGrammar.program =
  {functions = List.map p.functions ~f:from_external_func; body = from_external_expr p.body}


