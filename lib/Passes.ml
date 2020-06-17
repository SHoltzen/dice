(** Performs optimization passes over the core grammar **)

open Core
open Util
module EG = ExternalGrammar
module CG = CoreGrammar

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let inline_functions (p: EG.program) =
  let open EG in
  let function_map = List.fold p.functions ~init:(Map.Poly.empty) ~f:(fun acc f ->
      Map.Poly.add_exn acc ~key:f.name ~data:f) in
  let rec helper (e: EG.eexpr) =
    match e with
    | And(s, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in And(s, s1, s2)
    | Or(s, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Or(s, s1, s2)
    | Iff(s, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Eq(s, s1, s2)
    | IntConst(_, _) -> e
    | Plus(s, e1, e2) -> Plus(s, helper e1, helper e2)
    | Eq(s, e1, e2) -> Eq(s, helper e1, helper e2)
    | Neq(s, e1, e2) -> Neq(s, helper e1, helper e2)
    | Minus(s, e1, e2) -> Minus(s, helper e1, helper e2)
    | Mult(s, e1, e2) -> Mult(s, helper e1, helper e2)
    | Div(s, e1, e2) -> Div(s, helper e1, helper e2)
    | Lt(s, e1, e2) -> Lt(s, helper e1, helper e2)
    | Lte(s, e1, e2) -> helper(Or(s, Lt(s, e1, e2), Eq(s, e1, e2)))
    | Gt(s, e1, e2) -> helper(Not(s, Lte(s, e1, e2)))
    | Gte(s, e1, e2) -> helper(Not(s, Lt(s, e1, e2)))
    | Not(s, e) -> Not(s, helper e)
    | Flip(s, f) -> Flip(s, f)
    | Ident(s, id) -> Ident(s, id)
    | Discrete(s, l) -> Discrete(s, l)
    | Int(s, sz, v) -> Int(s, sz, v)
    | True(s) -> True(s)
    | False(s) -> False(s)
    | Observe(s, e) -> Observe(s, helper e)
    | Let(s, x, e1, e2) -> Let(s, x, helper e1, helper e2)
    | Ite(s, g, thn, els) -> Ite(s, helper g, helper thn, helper els)
    | Snd(s, e) -> Snd(s, helper e)
    | Fst(s, e) -> Fst(s, helper e)
    | Tup(s, e1, e2) -> Tup(s, helper e1, helper e2)
    | Iter(s, f, init, k) ->
      List.fold (List.init k ~f:(fun _ -> ())) ~init:init
        ~f:(fun acc _ -> FuncCall(s, f, [acc]))
    | FuncCall(s, id, args) ->
      let cur_f = Map.Poly.find_exn function_map id in
      let inlined = helper cur_f.body in
      List.fold (List.zip_exn cur_f.args args) ~init:inlined ~f:(fun acc (arg, v) -> Let(s, fst arg, v, acc)) in
  {functions=[]; body=helper p.body}

let num_paths (p: EG.program) : LogProbability.t =
  let inlined = inline_functions p in
  let rec helper (e: EG.eexpr) =
    match e with
    | And(_,e1, e2)
    | Or(_,e1, e2)
    | Plus(_,e1, e2)
    | Eq(_,e1, e2)
    | Minus(_,e1, e2)
    | Neq(_,e1, e2)
    | Div(_,e1, e2)
    | Mult(_,e1, e2)
    | Lt(_,e1, e2)
    | Gt(_,e1, e2)
    | Lte(_,e1, e2)
    | Gte(_,e1, e2)
    | Tup(_,e1, e2)
    | Let(_,_, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in LogProbability.mult s1 s2
    | Not(_,e) -> helper e
    | Flip(_,_) -> LogProbability.make 2.0
    | Ident(_,_) ->  LogProbability.make 1.0
    | Discrete(_,l) -> LogProbability.make (float_of_int (List.length l))
    | Int(_,_, _) -> LogProbability.make 1.0
    | True(_) -> LogProbability.make 1.0
    | False(_) -> LogProbability.make 1.0
    | Observe(_,e) -> helper e
    | Ite(_,g, thn, els) ->
      let gc = helper g in
      let tc = helper thn in
      let ec = helper els in
      LogProbability.mult gc (LogProbability.add tc ec)
    | Snd(_,e) | Fst(_, e) -> helper e
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
  let open CG in
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
    CG.Tup(x, mk_dfs_tuple xs)

let rec type_eq t1 t2 =
  let open EG in
  match (t1, t2) with
  | (TBool, TBool) -> true
  | ((TTuple(ll, lr), TTuple(rl, rr))) ->
    (type_eq ll rl) && (type_eq lr rr)
  | (TInt(d1), TInt(d2)) when d1 = d2 -> true
  | _ -> false

type source = EG.source
[@@deriving sexp_of]

type ast =
    And of source * tast * tast
  | Or of source * tast * tast
  | Iff of source * tast * tast
  | IntConst of source * int
  | Not of source * tast
  | Ite of source * tast * tast * tast
  | Flip of source * float
  | Let of source * String.t * tast * tast
  | Observe of source * tast
  | Ident of source * String.t
  | Discrete of source * float List.t
  | Int of source * int * int (* value, size *)
  | Eq of source * tast * tast
  | Plus of source * tast * tast
  | Minus of source * tast * tast
  | Mult of source * tast * tast
  | Div of source * tast * tast
  | Lte of source * tast * tast
  | Lt of source * tast * tast
  | Gte of source * tast * tast
  | Gt of source * tast * tast
  | Neq of source * tast * tast
  | Fst of source * tast
  | Snd of source * tast
  | Tup of source * tast * tast
  | FuncCall of source * String.t * tast List.t
  | Iter of source * String.t * tast * int
  | True of source
  | False of source
and
  tast = EG.typ * ast
[@@deriving sexp_of]

type arg = EG.arg
[@@deriving sexp_of]

type func = { name: String.t; args: arg List.t; body: tast}
[@@deriving sexp_of]

type program = { functions: func List.t; body: tast }
[@@deriving sexp_of]


let rec type_of (env: EG.tenv) (e: EG.eexpr) : tast =
  let open EG in
  let expect_t e (src: EG.lexing_position) typ : tast =
    let (t, e) = type_of env e in
    if (type_eq t typ) then (t, e) else
      raise (EG.Type_error(Format.sprintf "Type error at line %d column %d: expected %s, got %s"
                                      src.pos_lnum src.pos_cnum (EG.string_of_typ typ) (EG.string_of_typ t))) in
  let expect_compatible_int (f: tast -> tast -> ast) src e1 e2 =
    let (t1, s1) = type_of env e1 and (t2, s2) = type_of env e2 in
    match (t1, t2) with
    | (TInt(d1), TInt(d2)) when d1 = d2 -> (d1, f (t1, s1) (t1, s2))
    | (_, _) ->
      raise (EG.Type_error(Format.sprintf "Type error at line %d column %d: expected compatible integer types, got %s and %s"
                             src.pos_lnum src.pos_cnum (EG.string_of_typ t1) (EG.string_of_typ t2)))  in
  match e with
  | And(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, And(s, s1, s2))
  | Or(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, Or(s, s1, s2))
  | Iff(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, Iff(s, s1, s2))
  | Not(s, e1) ->
    let s1 = expect_t e1 s.startpos TBool in
    (TBool, Not(s, s1))
  | Observe(s, e1) ->
    let s1 = expect_t e1 s.startpos TBool in
    (TBool, Observe(s, s1))
  | True(s) -> (TBool, True(s))
  | False(s) -> (TBool, False(s))
  | Flip(s, f) -> (TBool, Flip(s,f))
  | Ident(src, s) ->
    let t = (try Map.Poly.find_exn env s
     with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: \
                                         Could not find variable '%s' during typechecking"
                                    src.startpos.pos_lnum src.startpos.pos_cnum s))) in
    (t, Ident(src, s))
  | Fst(s, e1) ->
    let (t, s1) = type_of env e1 in
    let t' = (match t with
     | TTuple(l, _) -> l
     | t -> raise (Type_error (Format.sprintf "Type error at line %d column %d: expected tuple, got %s"
                                 s.startpos.pos_lnum s.startpos.pos_cnum (string_of_typ t)))) in
    (t', Fst(s, (t, s1)))
  | Snd(s, e1) ->
    let s1 = type_of env e1 in
    let t = (match fst s1 with
     | TTuple(_, r) -> r
     | t -> raise (Type_error (Format.sprintf "Type error at line %d column %d: expected tuple, got %s"
                                 s.startpos.pos_lnum s.startpos.pos_cnum (string_of_typ t)))) in
    (t, Snd(s, s1))
  | Tup(s, e1, e2) ->
    let t1 = type_of env e1 in
    let t2 = type_of env e2 in
    (TTuple(fst t1, fst t2), Tup(s, t1, t2))
  | Int(src, sz, v) -> (TInt(sz), Int(src, sz, v))
  | Discrete(src, l) ->
    let sum = List.fold l ~init:0.0 ~f:(fun acc i -> acc +. i) in
    let within_epsilon x y =
      (Float.compare (Float.abs (x -. y)) 0.0001) < 0 in
    if not (within_epsilon sum 1.0) then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: discrete parameters must sum to 1, got %f"
                           src.startpos.pos_lnum src.startpos.pos_cnum sum))
    else (TInt(num_binary_digits ((List.length l) - 1)), Discrete(src, l))
  | Eq(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun s1 s2 -> Eq(s, s1, s2)) s.startpos e1 e2))
  | Lt(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Lt(s, e1, e2)) s.startpos e1 e2))
  | Gt(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Gt(s, e1, e2)) s.startpos e1 e2))
  | Lte(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Lte(s, e1, e2)) s.startpos e1 e2))
  | Gte(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Gte(s, e1, e2)) s.startpos e1 e2))
  | Neq(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Neq(s, e1, e2)) s.startpos e1 e2))
  | Plus(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Plus(s, e1, e2)) s.startpos e1 e2 in
    (TInt(sz), res)
  | Minus(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Minus(s, e1, e2)) s.startpos e1 e2 in
    (TInt(sz), res)
  | Mult(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Mult(s, e1, e2)) s.startpos e1 e2 in
    (TInt(sz), res)
  | Div(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Div(s, e1, e2)) s.startpos e1 e2 in
    (TInt(sz), res)
  | Let(slet, x, e1, e2) ->
    let r1 = type_of env e1 in
    let r2 = type_of (Map.Poly.set env ~key:x ~data:(fst r1)) e2 in
    (fst r2, Let(slet, x, r1, r2))
  | Ite(s, g, thn, els) ->
    let sg = expect_t g ((EG.get_src g).startpos) TBool in
    let (t1, thnbody) = type_of env thn and (t2, elsbody) = type_of env els in
    if not (type_eq t1 t2) then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: expected equal types \
                                         from branches of if-statement, got %s and %s"
                           s.startpos.pos_lnum s.startpos.pos_cnum (string_of_typ t1) (string_of_typ t2)))
    else (t1, Ite(s, sg, (t1, thnbody), (t2, elsbody)))
  | FuncCall(s, id, args) ->
    let res = try Map.Poly.find_exn env id
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could not find function \
                                                   '%s' during typechecking"
                                     s.startpos.pos_lnum s.startpos.pos_cnum id)) in
    let (targ, tres) = (match res with
        | TFunc(targ, tres) -> targ, tres
        | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: non-function type found for \
                                                   '%s' during typechecking, found %s "
                                     s.startpos.pos_lnum s.startpos.pos_cnum id (string_of_typ res)))) in
    let zipped = try List.zip_exn args targ
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could incompatible argument length, expected \
                                                   %d arguments and got %d arguments"
                                     s.startpos.pos_lnum s.startpos.pos_cnum (List.length targ) (List.length args))) in
    let arg' = List.mapi zipped ~f:(fun idx (arg, typ) ->
        let (found_t, body) = type_of env arg in
        if (type_eq found_t typ) then (found_t, body) else
          raise (Type_error (Format.sprintf "Type error in argument %d at line %d column %d: expected type %s, got %s"
                               s.startpos.pos_lnum s.startpos.pos_cnum (idx + 1) (string_of_typ typ) (string_of_typ found_t)))
      ) in
    (tres, FuncCall(s, id, arg'))
  | IntConst(_, _) -> failwith "Internal Error: unstripped int const"
  | Iter(s, id, init, _) ->
    let res = try Map.Poly.find_exn env id
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could not find function \
                                                   '%s' during typechecking"
                                     s.startpos.pos_lnum s.startpos.pos_cnum id)) in
    let (targ, tres) = (match res with
        | TFunc(targ, tres) -> targ, tres
        | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: non-function type found for \
                                                   '%s' during typechecking, found %s "
                                     s.startpos.pos_lnum s.startpos.pos_cnum id (string_of_typ res)))) in
    let (tinit, initbody) = type_of env init in
    (* TODO check arg validity*)
    (tres, initbody)


let rec and_of_l l =
  match l with
  | [] -> CG.True
  | [x] -> x
  | x::xs -> CG.And(x, and_of_l xs)

let rec gen_discrete (l: float List.t) =
  let open Cudd in
  let open CG in
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


let rec nth_snd i inner =
  match i with
    0 -> inner
  | n -> CG.Snd (nth_snd (n-1) inner)

let nth_bit sz n e : CG.expr = if n = sz-1 then nth_snd n (e) else Fst(nth_snd n (e))

let gen_adder sz a b : CG.expr =
  let a_name = fresh () in
  let b_name = fresh () in
  let tmp_a = CG.Ident(a_name) in
  let tmp_b = CG.Ident(b_name) in
  let carryname = Format.sprintf "carry%s" (fresh ()) in
  let outputname = Format.sprintf "output%s" (fresh ()) in
  let halfout = (Format.sprintf "%s_0" outputname, CG.Xor(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  let halfcarry = (Format.sprintf "%s_0" carryname, CG.And(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  (* very finnicky business in here ... generate a sequence of full adders
     that feed one into the next *)
  let fulladders = List.init (sz - 1) ~f:(fun bit ->
      let curidx = bit + 1 in
      let curbit = sz - bit - 2 in
      let curout = Format.sprintf "%s_%d" outputname curidx in
      let curinput_a = nth_bit sz curbit tmp_a in
      let curinput_b = nth_bit sz curbit tmp_b in
      let prevcarry = Format.sprintf "%s_%d" carryname (curidx - 1) in
      let curcarry = Format.sprintf "%s_%d" carryname curidx in
      [(curout, CG.Xor(Ident(prevcarry), CG.Xor(curinput_a, curinput_b)));
       (curcarry, CG.Or(CG.And(Ident(prevcarry), curinput_a),
                        CG.Or(CG.And(Ident(prevcarry), curinput_b), CG.And(curinput_a, curinput_b))))]
    ) |> List.concat in
  let full_l = [(a_name, a); (b_name, b); halfout; halfcarry] @ fulladders in
  let output_list = List.init sz ~f:(fun idx -> CG.Ident(Format.sprintf "%s_%d" outputname (sz - 1 - idx))) in
  let inner = mk_dfs_tuple output_list in
  List.fold_right full_l ~init:inner ~f:(fun (name, e) acc -> CG.Let(name, e, acc))

(* generates a subtractor circuit for a - b *)
let gen_subtractor sz a b : CG.expr =
  let a_name = fresh () in
  let b_name = fresh () in
  let tmp_a = CG.Ident(a_name) in
  let tmp_b = CG.Ident(b_name) in
  let borrowname = Format.sprintf "borrow%s" (fresh ()) in
  let outputname = Format.sprintf "output%s" (fresh ()) in
  let halfout = (Format.sprintf "%s_0" outputname, CG.Xor(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  let halfborrow = (Format.sprintf "%s_0" borrowname, CG.And(Not(nth_bit sz (sz-1) tmp_a), nth_bit sz (sz-1) tmp_b)) in
  (* very finnicky business in here ... generate a sequence of full adders
     that feed one into the next *)
  let fulladders = List.init (sz - 1) ~f:(fun bit ->
      let curidx = bit + 1 in
      let curbit = sz - bit - 2 in
      let curout = Format.sprintf "%s_%d" outputname curidx in
      let curinput_a = nth_bit sz curbit tmp_a in
      let curinput_b = nth_bit sz curbit tmp_b in
      let prevborrow = Format.sprintf "%s_%d" borrowname (curidx - 1) in
      let curborrow = Format.sprintf "%s_%d" borrowname curidx in
      [(curout, CG.Xor(Ident(prevborrow), CG.Xor(curinput_a, curinput_b)));
       (curborrow, CG.Or(CG.And(Ident(prevborrow), Not(curinput_a)),
                        CG.Or(CG.And(Ident(prevborrow), curinput_b), CG.And(Not(curinput_a), curinput_b))))]
    ) |> List.concat in
  let full_l = [(a_name, a); (b_name, b); halfout; halfborrow] @ fulladders in
  let output_list = List.init sz ~f:(fun idx -> CG.Ident(Format.sprintf "%s_%d" outputname (sz - 1 - idx))) in
  let inner = mk_dfs_tuple output_list in
  List.fold_right full_l ~init:inner ~f:(fun (name, e) acc -> CG.Let(name, e, acc))




let rec from_external_expr_h (tenv: EG.tenv) ((t, e): tast) : CG.expr =
  match e with
  | And(_, e1, e2) ->
    let s1 = from_external_expr_h tenv e1 in
    let s2 = from_external_expr_h tenv e2 in And(s1, s2)
  | Or(_, e1, e2) ->
    let s1 = from_external_expr_h tenv e1 in
    let s2 = from_external_expr_h tenv e2 in Or(s1, s2)
  | Iff(_, e1, e2) ->
    let s1 = from_external_expr_h tenv e1 in
    let s2 = from_external_expr_h tenv e2 in Eq(s1, s2)
  | Plus(_, e2, e1) ->
    let sz = (match t with
        | TInt(sz) -> sz
        | _ -> failwith "Internal Error: unreachable") in
    gen_adder sz (from_external_expr_h tenv e1) (from_external_expr_h tenv e2)
  | Minus(_, e1, e2) ->
    let sz = (match t with
        | TInt(sz) -> sz
        | _ -> failwith "Internal Error: unreachable") in
    gen_subtractor sz (from_external_expr_h tenv e1) (from_external_expr_h tenv e2)
  | Eq(_, (t1, e1), (t2, e2)) ->
    let sz = (match (t1, t2) with
        | EG.TInt(a), EG.TInt(b) when a = b -> a
        | _ -> failwith "Internal Error: Unreachable") in
    let n1 = fresh () and n2 = fresh () in
    let inner = List.init sz ~f:(fun idx ->
        CG.Eq(nth_bit sz idx (Ident(n1)), nth_bit sz idx (Ident(n2)))
      ) |> and_of_l in
    Let(n1, from_external_expr_h tenv (t1, e1), Let(n2, from_external_expr_h tenv (t2, e2), inner))
  | Neq(s, e1, e2) -> from_external_expr_h tenv (TBool, Not(s, (TBool, Eq(s, e1, e2))))
  | Mult(s, e1, e2) -> failwith "not implemented *"
  | Div(s, e1, e2) -> failwith "not implemented /"
  | Lt(_, (t1, e1), (t2, e2)) ->
    let sz = (match (t1, t2) with
        | EG.TInt(a), EG.TInt(b) when a = b -> a
        | _ -> failwith "Internal Error: Unreachable") in
    let n1 = fresh () and n2 = fresh () in
    let rec h idx : CG.expr =
      if idx = sz then False
      else Ite(And(nth_bit sz idx (Ident(n1)), Not(nth_bit sz idx (Ident n2))),
               False,
               Ite(And(Not(nth_bit sz idx (Ident(n1))), nth_bit sz idx (Ident n2)), True,
               h (idx + 1))) in
    Let(n1, from_external_expr_h tenv (t1, e1), Let(n2, from_external_expr_h tenv (t2, e2), h 0))
  | Lte(s, e1, e2) -> from_external_expr_h tenv (TBool, Or(s, (TBool, Lt(s, e1, e2)), (TBool, Eq(s, e1, e2))))
  | Gt(s, e1, e2) -> from_external_expr_h tenv (TBool, Not(s, (TBool, Lte(s, e1, e2))))
  | Gte(s, e1, e2) -> from_external_expr_h tenv (TBool, Not(s, (TBool, Lt(s, e1, e2))))
  | Not(s, e) -> Not(from_external_expr_h tenv e)
  | Flip(s, f) -> Flip(f)
  | Ident(src, s) -> Ident(s)
  | Discrete(s, l) -> gen_discrete l
  | Int(s, sz, v) ->
    let bits = int_to_bin sz v
               |> List.map ~f:(fun i -> if i = 1 then CG.True else CG.False) in
    mk_dfs_tuple bits
  | True(_) -> True
  | False(_) -> False
  | Observe(s, e) ->
    Observe(from_external_expr_h tenv e)
  | Let(s, x, e1, e2) ->
    let tenv' = Map.Poly.set tenv ~key:x ~data:t in
    Let(x, from_external_expr_h tenv e1, from_external_expr_h tenv' e2)
  | Ite(s, g, thn, els) -> Ite(from_external_expr_h tenv g, from_external_expr_h tenv thn, from_external_expr_h tenv els)
  | Snd(s, e) -> Snd(from_external_expr_h tenv e)
  | Fst(s, e) -> Fst(from_external_expr_h tenv e)
  | Tup(s, e1, e2) -> Tup(from_external_expr_h tenv e1, from_external_expr_h tenv e2)
  | FuncCall(s, id, args) -> FuncCall(id, List.map args ~f:(fun i -> from_external_expr_h tenv i))
  | Iter(s, f, init, k) ->
    let e = from_external_expr_h tenv init in
    List.fold (List.init k ~f:(fun _ -> ()))  ~init:e
      ~f:(fun acc _ -> FuncCall(f, [acc]))
  | IntConst(_, _) -> failwith "not implemented"

let from_external_expr (env: EG.tenv) (e: EG.eexpr) : (EG.typ * CG.expr) =
  let (typ, e) = type_of env e in
  (typ, from_external_expr_h Map.Poly.empty (typ, e))

let rec from_external_typ (t:EG.typ) : CG.typ =
  match t with
    TBool -> TBool
  | TInt(sz) ->
    let l = List.init sz ~f:(fun _ -> CG.TBool) in
    let rec mk_dfs_typ l =
      match l with
      | [] -> failwith "Internal Error: Invalid int type"
      | [x] -> x
      | x::xs ->
        CG.TTuple(x, mk_dfs_typ xs) in
    mk_dfs_typ l
  | TTuple(t1, t2) -> TTuple(from_external_typ t1, from_external_typ t2)
  | _ -> failwith "Internal Error: unreachable"

let from_external_arg (a:EG.arg) : CG.arg =
  let (name, t) = a in
  (name, from_external_typ t)

let from_external_func (tenv: EG.tenv) (f: EG.func) : (EG.typ * CG.func) =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let (t, conv) = from_external_expr tenvwithargs f.body in
  (* convert arguments *)
  let args = List.map f.args ~f:from_external_arg in
  (TFunc(List.map f.args ~f:snd, t), {name = f.name;
       args = args;
       body = conv})

let from_external_prog (p: EG.program) : CG.program =
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let (t, conv) = from_external_func tenv i in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let (_, convbody) = from_external_expr tenv p.body in
  {functions = functions; body = convbody}


