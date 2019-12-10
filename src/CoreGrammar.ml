open Core
open Cudd
open Wmc
open BddUtil

type expr =
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Ident of String.t
  | Fst of expr
  | Snd of expr
  | Tup of expr * expr
  | Ite of expr * expr * expr
  | True
  | False
  | Flip of float
  | Let of String.t * expr * expr
  | FuncCall of fcall
  | Observe of expr
[@@deriving sexp]

and fcall = {
  assgn: String.t List.t;
  fname: String.t;
  args: expr
}
[@@deriving sexp]

(** Core function grammar *)
type func = {
  name: String.t;
  args: String.t List.t;
  body: expr;
}
[@@deriving sexp]

type compiled_func = {
  args: Bdd.dt List.t;
  flips: Bdd.dt List.t;
}

type program = {
  functions: func List.t;
  body: expr;
}
[@@deriving sexp]

let rec from_external_expr (e: ExternalGrammar.eexpr) : expr =
  match e with
  | And(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in And(s1, s2)
  | Or(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Or(s1, s2)
  | Not(e) -> Not(from_external_expr e)
  | Flip(f) -> Flip(f)
  | Ident(s) -> Ident(s)
  | True -> True
  | False -> False
  | Observe(e) -> Observe(from_external_expr e)
  | Let(x, e1, e2) -> Let(x, from_external_expr e1, from_external_expr e2)
  | Ite(g, thn, els) -> Ite(from_external_expr g, from_external_expr thn, from_external_expr els)
  | Snd(e) -> Snd(from_external_expr e)
  | Fst(e) -> Fst(from_external_expr e)
  | Tup(e1, e2) -> Tup(from_external_expr e1, from_external_expr e2)

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

(** The result of compiling an expression. A pair (value, normalizing constant) *)
type state = (Bdd.dt btree * Bdd.dt)

let extract_bdd state =
  match state with
  | Leaf(bdd) -> bdd
  | _ -> failwith "invalid bdd extraction"

let rec map_tree (s:'a btree) (f: 'a -> 'b) : 'b btree =
  match s with
  | Leaf(bdd) -> Leaf(f bdd)
  | Node(l, r) -> Node(map_tree l f, map_tree r f)

let rec zip_tree (s1: 'a btree) (s2: 'b btree) =
  match (s1, s2) with
  | (Leaf(a), Leaf(b)) -> Leaf((a, b))
  | (Node(a_l, a_r), Node(b_l, b_r)) ->
    Node(zip_tree a_l b_l, zip_tree a_r b_r)
  | _ -> failwith "could not zip trees, incompatible shape"

type compile_context = {
  man: Man.dt;
  name_map: (int, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
}

type env = (String.t, Bdd.dt btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let new_context () =
  let man = Man.make_d () in
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man=man;
   name_map=names;
   weights= weights}

let rec compile_expr (ctx: compile_context) (env: env) e : state =
  match e with
  | And(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let v = Leaf(Bdd.dand (extract_bdd v1) (extract_bdd v2)) in
    let z =Bdd.dand z1 z2 in
    (v, z)
  | Or(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let v = Leaf(Bdd.dor (extract_bdd v1) (extract_bdd v2)) in
    let z =Bdd.dand z1 z2 in
    (v, z)
  | Not(e) ->
    let (v1, z1) = compile_expr ctx env e in
    let v = Bdd.dnot (extract_bdd v1) in
    (Leaf(v), z1)
  | True -> (Leaf(Bdd.dtrue ctx.man), Bdd.dtrue ctx.man)
  | False -> (Leaf(Bdd.dfalse ctx.man), Bdd.dtrue ctx.man)
  | Ident(s) ->
    (match Map.Poly.find env s with
     | Some(r) -> (r, Bdd.dtrue ctx.man)
     | _ -> failwith (sprintf "Could not find Boolean variable %s" s))
  | Tup(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    (Node(v1, v2), Bdd.dand z1 z2)
  | Ite(g, thn, els) ->
    let (vg, zg) = compile_expr ctx env g in
    let (vthn, zthn) = compile_expr ctx env thn in
    let (vels, zels) = compile_expr ctx env els in
    let gbdd = extract_bdd vg in
    let zipped = zip_tree vthn vels in
    let v' = map_tree zipped (fun (thn_bdd, els_bdd) ->
        Bdd.dor (Bdd.dand gbdd thn_bdd) (Bdd.dand (Bdd.dnot gbdd) els_bdd)
      ) in
    let z' = Bdd.dand zg (Bdd.dor (Bdd.dand zthn gbdd)
                            (Bdd.dand zels (Bdd.dnot gbdd))) in
    (v', z')
  | Fst(e) ->
    let (v, z) = compile_expr ctx env e in
    let v' = (match v with
     | Node(l, _) -> l
     | _ -> failwith "calling `fst` on non-tuple") in
    (v', z)
  | Snd(e) ->
    let (v, z) = compile_expr ctx env e in
    let v' = (match v with
     | Node(_, r) -> r
     | _ -> failwith "calling `snd` on non-tuple") in
    (v', z)
  | Flip(f) ->
    let new_f = Bdd.newvar ctx.man in
    let var_lbl = Bdd.topvar new_f in
    Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.f, f);
    Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "f%f" f);
    (Leaf(new_f), Bdd.dtrue ctx.man)
  | Observe(g) ->
    let (g, z) = compile_expr ctx env g in
    (Leaf(Bdd.dtrue ctx.man), Bdd.dand (extract_bdd g) z)
  | Let(x, e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let env' = Map.Poly.set env ~key:x ~data:v1 in
    let (v2, z2) = compile_expr ctx env' e2 in
    (v2, Bdd.dand z1 z2)
  | FuncCall(c) -> failwith "not impl"

let get_prob e =
  let ctx = new_context () in
  let env = Map.Poly.empty in
  let (v, zbdd) = compile_expr ctx env e in
  let z = Wmc.wmc zbdd ctx.weights in
  let prob = Wmc.wmc (extract_bdd v) ctx.weights in
  prob /. z
