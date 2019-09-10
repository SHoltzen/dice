open Core
open Cudd
open Wmc

(** Atomic expression. Expressions that are pure and cannot produce a
    distribution or affect the state of the program. *)
type aexpr =
  | And of aexpr * aexpr
  | Or of aexpr * aexpr
  | Not of aexpr
  | Ident of String.t
  | Fst of aexpr
  | Snd of aexpr
  | Tup of aexpr * aexpr
  | True
  | False
[@@deriving sexp]

(** Core expression type *)
type expr =
    Flip of float
  | Ite of aexpr * expr * expr
  | Let of String.t * aexpr * expr
  | FuncCall of fcall
  | Observe of aexpr * expr
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

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

type state = Bdd.dt btree

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

(* TODO make `weights` a map, to get scoping right*)
type compile_context = {
  man: Man.dt;
  vstate: (String.t, state) Hashtbl.Poly.t; (* map from variable identifiers to BDDs*)
  weights: weight; (* map from variables to weights *)
  evalind: Bdd.dt; (* special Boolean variable that holds the result of an expression *)
}

let rec compile_aexpr (ctx: compile_context) e : state =
  match e with
  | And(e1, e2) ->
    let s1 = extract_bdd (compile_aexpr ctx e1) in
    let s2 = extract_bdd (compile_aexpr ctx e2) in
    Leaf(Bdd.dand s1 s2)
  | Or(e1, e2) ->
    let s1 = extract_bdd (compile_aexpr ctx e1) in
    let s2 = extract_bdd (compile_aexpr ctx e2) in
    Leaf(Bdd.dor s1 s2)
  | Not(e) ->
    let v = Bdd.dnot (extract_bdd (compile_aexpr ctx e)) in
    Leaf(v)
  | True -> Leaf(Bdd.dtrue ctx.man)
  | False -> Leaf(Bdd.dfalse ctx.man)
  | Ident(s) ->
    (match Hashtbl.Poly.find ctx.vstate s with
     | Some(r) -> r
     | _ -> failwith (sprintf "Could not find Boolean variable %s" s))
  | Tup(e1, e2) ->
    let c1 = compile_aexpr ctx e1 in
    let c2 = compile_aexpr ctx e2 in
    Node(c1, c2)
  | Fst(e) ->
    let c = compile_aexpr ctx e in
    (match c with
     | Node(l, _) -> l
     | _ -> failwith "calling `fst` on non-tuple")
  | Snd(e) ->
    let c = compile_aexpr ctx e in
    (match c with
     | Node(_, r) -> r
     | _ -> failwith "calling `snd` on non-tuple")

let rec compile_expr (ctx:compile_context) s : state =
  match s with
  | Flip(f) ->
    let new_f = Bdd.newvar ctx.man in
    let var_lbl = Bdd.topvar new_f in
    Hashtbl.Poly.add_exn ctx.weights var_lbl (f, 1.0-.f);
    let r = Bdd.eq new_f ctx.evalind in
    Leaf(r)
  | Observe(g, e) ->
    let v = compile_expr ctx e in
    let g = extract_bdd (compile_aexpr ctx g) in
    map_tree v (fun bdd ->
        Bdd.dand g bdd
      )
  | Ite(guard, thn, els) ->
    let compthn = compile_expr ctx thn in
    let compels = compile_expr ctx els in
    let compg = extract_bdd (compile_aexpr ctx guard) in
    let zipped = zip_tree compthn compels in
    map_tree zipped (fun (thn_bdd, els_bdd) ->
        Bdd.dor (Bdd.dand compg thn_bdd) (Bdd.dand (Bdd.dnot compg) els_bdd)
      )
  | Let(s, e1, e2) ->
    let c = compile_aexpr ctx e1 in
    Hashtbl.add_exn ctx.vstate s c;
    compile_expr ctx e2
  | FuncCall(c) -> failwith "not impl"
