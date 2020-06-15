(** Performs optimization passes over the core grammar **)

open Core
open Util

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let inline_functions (p: ExternalGrammar.program) =
  let open ExternalGrammar in
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

let num_binary_digits d = int_of_float (floor (Util.log2 (float_of_int (d)))) + 1

(** produces all binary sequences up to a size [sz] *)
let rec all_binary sz =
  assert (sz >= 0);
  match sz with
  | 0 -> [[]]
  | n ->
    let subl = all_binary (n-1) in
    List.map subl ~f:(fun i -> i @ [1]) @
    List.map subl ~f:(fun i -> i @ [0])

(** converts a little-endian binary vector into an integer *)
let bin_to_int l =
  let sz = (List.length l) - 1 in
  List.foldi l ~init:0 ~f:(fun idx acc i -> acc + (i lsl (sz - idx)) )

(** converts a little-endian binary vector into an integer *)
let int_to_bin final_sz d =
  let rec helper cur_pos d =
    if cur_pos >= 0 then
      let cur_v = 1 lsl cur_pos in
      let p' = cur_pos - 1 in
      if d < cur_v then [0] @ (helper p' d) else [1] @ (helper p' (d - cur_v))
    else [] in
  let sz = (num_binary_digits d) - 1 in
  let r = helper sz d in
  let padding = List.init (final_sz - List.length r) ~f:(fun _ -> 0) in
  padding @ r

(** builds a list of all assignments to `l`, a list of (expr, bdd) *)
let rec all_assignments mgr l =
  let open Cudd in
  let open CoreGrammar in
  match l with
  | [] -> [True, Bdd.dtrue mgr]
  | (cur_constraint, cur_bdd)::xs ->
    let l1 = List.map (all_assignments mgr xs)
        ~f:(fun (constr, bdd) -> And(cur_constraint, constr), Bdd.dand cur_bdd bdd) in
    let l2 = List.map (all_assignments mgr xs)
        ~f:(fun (constr, bdd) -> And(Not(cur_constraint), constr), Bdd.dand (Bdd.dnot cur_bdd) bdd) in
    l1 @ l2

let fold_with_seen l ~init ~f =
  let (_, r) = List.fold l ~init:(([], init)) ~f:(fun (seen, acc) i ->
      let r = f seen acc i in
      ([i] @ seen, r)) in
  r

(* given a list of expressions [e1; e2; e3; ..] makes a
   tuple that looks like (e1, (e2, (e3, ...)))*)
let rec mk_dfs_tuple l =
  match l with
  | [] -> failwith "cannot call with empty list"
  | [x] -> x
  | x::xs ->
    CoreGrammar.Tup(x, mk_dfs_tuple xs)

let rec gen_discrete (l: float List.t) =
  let open Cudd in
  let open CoreGrammar in
  (* first generate the ADD *)
  let mgr = Man.make_d () in
  (* list of bits in little-endian order *)
  let bits = List.init (num_binary_digits ((List.length l) - 1)) ~f:(fun i -> (Ident(Format.sprintf "d%d" i), Bdd.newvar mgr)) in
  let numbits = List.length bits in
  let bitcube = List.fold bits ~init:(Bdd.dtrue mgr) ~f:(fun acc i -> Bdd.dand acc (snd i)) in
  let add = List.foldi l ~init:(Add.cst mgr 0.0) ~f:(fun idx acc param ->
      let bitvec = List.zip_exn (int_to_bin numbits idx) (bits) in
      let indicator = List.fold bitvec ~init:(Bdd.dtrue mgr) ~f:(fun acc (v, (_, b)) ->
          let curv = if v = 1 then b else Bdd.dnot b in
          Bdd.dand acc curv
        ) in
      let leaf = Add.cst mgr param in
      Add.ite indicator leaf acc
    ) in
  (* now make the list of flip assignments *)
  let sum_add a = Add.dval (Add.exist bitcube a) in
  let assgn = fold_with_seen bits ~init:[] ~f:(fun seen acc (cur_name, cur_bit) ->
      let all_assgn = all_assignments mgr seen in
      let l = List.map all_assgn ~f:(fun (cur_constraint, cur_bdd) ->
          let p1 = sum_add (Add.mul add (Add.of_bdd (Bdd.dand cur_bit cur_bdd))) in
          let p2 = sum_add (Add.mul add (Add.of_bdd (Bdd.dand cur_bdd (Bdd.dnot cur_bit)))) in
          if within_epsilon p1 0.0 then
            (cur_constraint, 0.)
          else
            (cur_constraint, (p1 /. (p1 +. p2)))
        ) in
      (* now build the expression *)
      (match l with
       | [] -> failwith "unreachable"
       | [(_, param)] -> [cur_name, Flip(param)]
       | (_, param)::xs ->
         let ifbody = List.fold xs ~init:(Flip(param)) ~f:(fun acc (guard, param) -> Ite(guard, Flip(param), acc)) in
         [cur_name, ifbody]
      ) @ acc
    ) in
  (* now finally build the entire let assignment *)
  let inner_body = mk_dfs_tuple (List.map bits ~f:fst) in
  List.fold assgn ~init:inner_body ~f:(fun acc (Ident(name), body) -> Let(name, body, acc))


let rec type_of (env: ExternalGrammar.tenv) (e: ExternalGrammar.eexpr) : ExternalGrammar.typ =
  match e with
  | And(_, _) | Or(_, _) | Not(_) | True | False | Flip(_) | Observe(_) -> TBool
  | Ident(s) -> (try Map.Poly.find_exn env s
    with _ -> failwith (Format.sprintf "Could not find variable %s during typechecking" s))
  | Fst(e1) ->
    (match type_of env e1 with
     | TTuple(l, _) -> l
     | _ -> failwith "Type error: expected tuple")
  | Snd(e1) ->
    (match type_of env e1 with
     | TTuple(_, r) -> r
     | _ -> failwith "Type error: expected tuple")
  | Tup(e1, e2) ->
    let t1 = type_of env e1 in
    let t2 = type_of env e2 in
    TTuple(t1 ,t2)
  | Int(sz, v) -> TInt(num_binary_digits sz)
  | Discrete(l) -> TInt(num_binary_digits (List.length l))
  | Eq(_, _) | Lt(_, _) | Gt(_, _) | Lte(_, _) | Gte(_,_) | Neq(_, _) -> TBool
  | Plus(l,_) | Minus(l,_) | Mult(l,_) | Div(l,_) ->
    type_of env l
  | Let(x, e1, e2) ->
    let te1 = type_of env e1 in
    type_of (Map.Poly.set env ~key:x ~data:te1) e2
  | Ite(_, thn, _) ->
    let t1 = type_of env thn in
    (* let t2 = type_of env els in *)
    (* assert (t1 == t2); *)
    t1
  | FuncCall(id, _) ->
    (try Map.Poly.find_exn env id
    with _ -> failwith (Format.sprintf "Could not find function '%s' during typechecking" id))

let rec nth_snd i inner =
  match i with
    0 -> inner
  | n -> CoreGrammar.Snd (nth_snd (n-1) inner)

let rec and_of_l l =
  match l with
  | [] -> CoreGrammar.True
  | [x] -> x
  | x::xs -> CoreGrammar.And(x, and_of_l xs)

let rec from_external_expr_h (tenv: ExternalGrammar.tenv) (e: ExternalGrammar.eexpr) : CoreGrammar.expr =
  match e with
  | And(e1, e2) ->
    let s1 = from_external_expr_h tenv e1 in
    let s2 = from_external_expr_h tenv e2 in And(s1, s2)
  | Or(e1, e2) ->
    let s1 = from_external_expr_h tenv e1 in
    let s2 = from_external_expr_h tenv e2 in Or(s1, s2)
  | Plus(e1, e2) -> failwith "not implemented +"
  | Eq(e1, e2) ->
    let t1 = type_of tenv e1 in
    let t2 = type_of tenv e2 in
    let sz = (match (t1, t2) with
        | ExternalGrammar.TInt(a), ExternalGrammar.TInt(b) when a = b -> a
        | _ -> failwith (Format.sprintf "Type error at %s" (ExternalGrammar.string_of_eexpr e))) in
    let n1 = fresh () and n2 = fresh () in
    let inner = List.init sz ~f:(fun idx ->
        if idx = sz-1 then
          CoreGrammar.Eq( nth_snd idx (Ident(n1)),
                          nth_snd idx (Ident(n2))) else
          CoreGrammar.Eq(Fst (nth_snd idx (Ident(n1))),
                         Fst(nth_snd idx (Ident(n2))))
      ) |> and_of_l in
    Let(n1, from_external_expr_h tenv e1, Let(n2, from_external_expr_h tenv e2, inner))
  | Neq(e1, e2) -> from_external_expr_h tenv (Not (Eq (e1, e2)))
  | Minus(e1, e2) -> failwith "not implemented -"
  | Mult(e1, e2) -> failwith "not implemented *"
  | Div(e1, e2) -> failwith "not implemented /"
  | Lt(e1, e2) -> failwith "not implemented <"
  | Lte(e1, e2) -> from_external_expr_h tenv (Or(Lt(e1, e2), Eq(e1, e2)))
  | Gt(e1, e2) -> from_external_expr_h tenv (Not(Lte(e1, e2)))
  | Gte(e1, e2) -> from_external_expr_h tenv (Not(Lt(e1, e2)))
  | Not(e) -> Not(from_external_expr_h tenv e)
  | Flip(f) -> Flip(f)
  | Ident(s) -> Ident(s)
  | Discrete(l) -> gen_discrete l
  | Int(sz, v) ->
    let bits = int_to_bin sz v
               |> List.map ~f:(fun i -> if i = 1 then CoreGrammar.True else CoreGrammar.False) in
    mk_dfs_tuple bits
  | True -> True
  | False -> False
  | Observe(e) -> Observe(from_external_expr_h tenv e)
  | Let(x, e1, e2) ->
    let t = type_of tenv e1 in
    let tenv' = Map.Poly.set tenv ~key:x ~data:t in
    Let(x, from_external_expr_h tenv e1, from_external_expr_h tenv' e2)
  | Ite(g, thn, els) -> Ite(from_external_expr_h tenv g, from_external_expr_h tenv thn, from_external_expr_h tenv els)
  | Snd(e) -> Snd(from_external_expr_h tenv e)
  | Fst(e) -> Fst(from_external_expr_h tenv e)
  | Tup(e1, e2) -> Tup(from_external_expr_h tenv e1, from_external_expr_h tenv e2)
  | FuncCall(id, args) -> FuncCall(id, List.map args ~f:(fun i -> from_external_expr_h tenv i))
  | Iter(f, init, k) ->
    let e = from_external_expr_h tenv init in
    List.fold (List.init k ~f:(fun _ -> ()))  ~init:e
      ~f:(fun acc _ -> FuncCall(f, [acc]))

let from_external_expr (e: ExternalGrammar.eexpr) : CoreGrammar.expr = from_external_expr_h Map.Poly.empty e

let rec from_external_typ (t:ExternalGrammar.typ) : CoreGrammar.typ =
  match t with
    TBool -> TBool
  | TInt(sz) -> failwith "not implemented"
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


