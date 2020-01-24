open Core
open Cudd

(** The result of compiling an expression. A pair (value, normalizing constant) *)
type varstate =
    BddLeaf of Bdd.dt
  | IntLeaf of Bdd.dt List.t

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

let extract_bdd (state: varstate btree) =
  match state with
  | Leaf(BddLeaf(bdd)) -> bdd
  | _ -> failwith "Type error: expected Boolean"

let extract_discrete (state: varstate btree) =
  match state with
  | Leaf(IntLeaf(l)) -> l
  | _ -> failwith "Type error: expected discrete"

(** applies `f` to each leaf in `s` *)
let rec map_tree (s:'a btree) (f: 'a -> 'b) : 'b btree =
  match s with
  | Leaf(bdd) -> Leaf(f bdd)
  | Node(l, r) -> Node(map_tree l f, map_tree r f)

(** Applies `f` to each BDD in `s` *)
let rec map_bddtree (s:varstate btree) (f: Bdd.dt -> Bdd.dt) : varstate btree =
  match s with
  | Leaf(BddLeaf(bdd)) -> Leaf(BddLeaf(f bdd))
  | Leaf(IntLeaf(l)) -> Leaf(IntLeaf(List.map l ~f:f))
  | Node(l, r) -> Node(map_bddtree l f, map_bddtree r f)

(** [fold_bddtree] folds [f] over each BDD in [s] with accumulator [acc] *)
let rec fold_bddtree (s:varstate btree) acc f =
  match s with
  | Leaf(BddLeaf(bdd)) -> f acc bdd
  | Leaf(IntLeaf(l)) -> List.fold l ~init: acc ~f:f
  | Node(l, r) ->
    let a_1 = fold_bddtree l acc f in
    fold_bddtree r a_1 f

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
    | Leaf(BddLeaf(bdd)) ->
      [(`True, bdd); (`False, Bdd.dnot bdd)]
    | Leaf(IntLeaf(l)) ->
      List.mapi l ~f:(fun i itm ->
          ((`Int(List.length l, i)), itm)
        )
    | Node(l, r) ->
      let lst = process_state l and rst = process_state r in
      List.map lst ~f:(fun (lt, lbdd) ->
          List.map rst ~f:(fun (rt, rbdd) ->
              (`Tup(lt, rt), Bdd.dand lbdd rbdd)
            )
        )
      |> List.concat in
  process_state st


(** [state_size] computes the total number of unique nodes in the list of
    varstates [states] *)
let state_size (states : varstate btree List.t) =
  let seen = Hash_set.Poly.create () in
  let rec helper (bdd : Bdd.dt) =
    match Hash_set.Poly.mem seen bdd with
    | true -> 0
    | false ->
      Hash_set.Poly.add seen bdd;
      (match Bdd.inspect bdd with
       | Bool(_) -> 1
       | Ite(_, l, r) -> 1 + (helper l) + (helper r)) in
  List.fold states ~init:0 ~f:(fun acc i -> fold_bddtree i acc (fun acc bdd ->
      acc + (helper bdd)))

(** [model_count] computes number of distinct models for the states in [states] *)
let model_count num_vars (states : varstate btree List.t) =
  let seen = Hashtbl.Poly.create () in
  let rec helper (bdd : Bdd.dt) cur_level =
    match Hashtbl.Poly.find seen bdd with
    | Some(v) -> v
    | None ->
      let v = (match Bdd.inspect bdd with
       | Bool(true) -> Int.pow 2 (Int.abs (num_vars - cur_level))
       | Bool(false) -> 0
       | Ite(level, l, r) ->
         (Int.pow 2 (Int.abs (level - cur_level))) * ((helper l cur_level) + (helper r level))) in
      Hashtbl.Poly.add_exn seen bdd v;
      v in
  List.fold states ~init:0 ~f:(fun acc i -> fold_bddtree i acc (fun acc bdd ->
      match Bdd.is_cst bdd with
      | true -> acc + 1
      | false -> acc + (helper bdd 0)))
