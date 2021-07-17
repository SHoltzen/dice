open Core
open Bdd

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

let rec not_leaves mgr = function
| Leaf bdd -> bdd_negate mgr bdd
| Node(l, r) -> bdd_and mgr (not_leaves mgr l) (not_leaves mgr r)

(** [get_table] gets a list of all possible instantiations of BDDs in [st]. *)
let get_table (cfg : Passes.config) mgr st typ =
  let rec process_state t state =
    let open ExternalGrammar in
    match (t, state) with
    | (TBool, Leaf(bdd)) ->
      [(`True, bdd); (`False, bdd_negate mgr bdd)]
    | (TInt(1), Leaf(bdd)) ->
      [`Int(0), bdd_negate mgr bdd; `Int(1), bdd;]
    | (TInt(sz), Node(Leaf(bdd), r)) ->
      let sub1 = process_state (TInt(sz-1)) r in
      let curbitvalue = 1 lsl (sz - 1) in
      let lower = List.map sub1 ~f:(fun (t, subbdd) ->
          match t with
            `Int(tval) -> `Int(tval), Bdd.bdd_and mgr (Bdd.bdd_negate mgr bdd) subbdd
          | _ -> failwith "Unreachable"
        ) in
      let upper = List.map sub1 ~f:(fun (t, subbdd) ->
          match t with
            `Int(tval) -> `Int(tval + curbitvalue), Bdd.bdd_and mgr bdd subbdd
          | _ -> failwith "Unreachable"
        ) in
      lower @ upper
    | (TTuple(t1, t2), Node(l, r)) ->
      let lst = process_state t1 l and rst = process_state t2 r in
      List.map lst ~f:(fun (lt, lbdd) ->
          List.map rst ~f:(fun (rt, rbdd) ->
              (`Tup(lt, rt), bdd_and mgr lbdd rbdd)
            )
        ) |> List.concat
    | (TList(elem_t), Node(len_state, elems_state)) ->
      let len_table = List.take
        (process_state (TInt (Util.bit_length cfg.max_list_length)) len_state)
        (succ cfg.max_list_length) in
      let rec process_list elems_len max_len s =
        match elems_len, max_len, s with
        | 0, _, _ -> [[], not_leaves mgr s]
        | 1, 1, _ -> List.map (process_state elem_t s) ~f:(fun (v, bdd) -> [v], bdd)
        | _, _, Node(x, xs) ->
          let x_table = process_state elem_t x in
          let xs_table = process_list (pred elems_len) (pred max_len) xs in
          List.concat_map x_table ~f:(fun (x_val, x_bdd) ->
            List.map xs_table ~f:(fun (xs_vals, xs_bdd) ->
              x_val :: xs_vals, bdd_and mgr x_bdd xs_bdd))
        | _ -> failwith "Unreachable" in
      List.concat_map len_table ~f:(fun (len_val, len_bdd) ->
        match len_val with
        | `Int(len) ->
          List.map (process_list len cfg.max_list_length elems_state)
            ~f:(fun (elems, elems_bdd) ->
              `List elems, bdd_and mgr len_bdd elems_bdd)
        | _ -> failwith "Unreachable")
    | _ -> failwith "Unreachable"
  in
  process_state typ st

let rec collect_leaves t =
  match t with
  | Leaf(a) -> [a]
  | Node(l, r) -> collect_leaves l @ collect_leaves r

(** [state_size] computes the total number of unique nodes in the list of
    varstates [states] *)
let state_size mgr (states : bddptr btree List.t) =
  let seen = Hash_set.Poly.create () in
  let rec helper (bdd : bddptr) =
    match Hash_set.Poly.mem seen bdd with
    | true -> 0
    | false ->
      Hash_set.Poly.add seen bdd;
      if Bdd.bdd_is_const mgr bdd then 1 else
        1 + (helper (Bdd.bdd_low mgr bdd)) + (helper (Bdd.bdd_high mgr bdd)) in
  List.fold states ~init:0 ~f:(fun acc i ->
      let leaves = collect_leaves i in
      List.fold leaves ~init:acc ~f:(fun acc bdd -> acc + (helper bdd)) )

(** substitute the variable x for the state `state` in f *)
let subst_state mgr (x: bddptr btree) (state: bddptr btree) (f: bddptr btree) =
  let newsubst = List.zip_exn (collect_leaves x) (collect_leaves state) in
  List.fold ~init:f newsubst ~f:(fun acc (tmp, e1c) ->
      map_tree acc (fun bdd ->
          Bdd.bdd_compose mgr  bdd (Bdd.bdd_topvar mgr tmp) e1c
        )
    )


