open Core
open Cudd

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

(** applies `f` to each leaf in `s` *)
let rec map_tree (s:'a btree) (f: 'a -> 'b) : 'b btree =
  match s with
  | Leaf(bdd) -> Leaf(f bdd)
  | Node(l, r) -> Node(map_tree l f, map_tree r f)

let rec iter_tree (s:'a btree) (f: 'a -> unit) =
  match s with
  | Leaf(bdd) -> f bdd
  | Node(l, r) ->
    iter_tree l f;
    iter_tree r f

let extract_leaf a =
  match a with
  | Leaf(a) -> a
  | _ -> failwith "Attempting to extract non-leaf node"

let rec zip_tree (s1: 'a btree) (s2: 'b btree) =
  match (s1, s2) with
  | (Leaf(a), Leaf(b)) -> Leaf((a, b))
  | (Node(a_l, a_r), Node(b_l, b_r)) ->
    Node(zip_tree a_l b_l, zip_tree a_r b_r)
  | _ -> failwith "could not zip trees, incompatible shape"

(** [get_table] gets a list of all possible instantiations of BDDs in [st]. *)
let get_table st =
  let rec process_state state =
    match state with
    | Leaf(bdd) ->
      [(`True, bdd); (`False, Bdd.dnot bdd)]
    | Node(l, r) ->
      let lst = process_state l and rst = process_state r in
      List.map lst ~f:(fun (lt, lbdd) ->
          List.map rst ~f:(fun (rt, rbdd) ->
              (`Tup(lt, rt), Bdd.dand lbdd rbdd)
            )
        )
      |> List.concat in
  process_state st

let rec collect_leaves t =
  match t with
  | Leaf(a) -> [a]
  | Node(l, r) -> collect_leaves l @ collect_leaves r

(** [state_size] computes the total number of unique nodes in the list of
    varstates [states] *)
let state_size (states : Bdd.dt btree List.t) =
  let seen = Hash_set.Poly.create () in
  let rec helper (bdd : Bdd.dt) =
    match Hash_set.Poly.mem seen bdd with
    | true -> 0
    | false ->
      Hash_set.Poly.add seen bdd;
      (match Bdd.inspect bdd with
       | Bool(_) -> 1
       | Ite(_, l, r) -> 1 + (helper l) + (helper r)) in
  List.fold states ~init:0 ~f:(fun acc i ->
      let leaves = collect_leaves i in
      List.fold leaves ~init:acc ~f:(fun acc bdd -> acc + (helper bdd)) )

