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
let get_table st typ =
  let rec process_state t state =
    let open ExternalGrammar in
    match (t, state) with
    | (TBool, Leaf(bdd)) ->
      [(`True, bdd); (`False, Bdd.dnot bdd)]
    | (TInt(1), Leaf(bdd)) ->
      [`Int(0), Bdd.dnot bdd; `Int(1), bdd;]
    | (TInt(sz), Node(Leaf(bdd), r)) ->
      let sub1 = process_state (TInt(sz-1)) r in
      let curbitvalue = 1 lsl (sz - 1) in
      let lower = List.map sub1 ~f:(fun (t, subbdd) ->
          match t with
            `Int(tval) -> `Int(tval), Bdd.dand (Bdd.dnot bdd) subbdd
          | _ -> failwith "Unreachable"
        ) in
      let upper = List.map sub1 ~f:(fun (t, subbdd) ->
          match t with
            `Int(tval) -> `Int(tval + curbitvalue), Bdd.dand bdd subbdd
          | _ -> failwith "Unreachable"
        ) in
      lower @ upper
    | (TTuple(t1, t2), Node(l, r)) ->
      let lst = process_state t1 l and rst = process_state t2 r in
      List.map lst ~f:(fun (lt, lbdd) ->
          List.map rst ~f:(fun (rt, rbdd) ->
              (`Tup(lt, rt), Bdd.dand lbdd rbdd)
            )
        ) |> List.concat
    | _ -> failwith "Unreachable"
  in
  process_state typ st

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


let rec subst_state_h tbl varset x state f =
  if Bdd.is_cst f then f else
    match Hashtbl.Poly.find tbl f with
    | Some(x) -> x
    | None ->
      let res = (match (x, state) with
       | ([], []) -> f
       | (x::xs, state::states) ->
         let var = Bdd.topvar f in
         (* if we have passed all variables *)
         if not (Set.Poly.mem varset var) then f
         else if var == x then
           (* subst for children, then compose in current variable *)
           let subst_thn = subst_state_h tbl varset xs states (Bdd.dthen f) in
           let subst_els = subst_state_h tbl varset xs states (Bdd.delse f) in
           Bdd.ite state subst_thn subst_els
         else if not (List.mem xs var ~equal:(==)) then
           failwith "Out of order"
         else
           (* skip this var,state pair *)
           subst_state_h tbl varset xs states f
       | _ -> failwith "unreachable"
        ) in
      let _x = Hashtbl.Poly.add tbl ~key:f ~data:res in
      res

(** substitute the variable x for the state `state` in f *)
let subst_state (x: Bdd.dt btree) (state: Bdd.dt btree) (f: Bdd.dt btree) =
  (* let tbl = Hashtbl.Poly.create () in
   * let xlst = (List.map ~f:Bdd.topvar (collect_leaves x)) in
   * let varset = Set.Poly.of_list xlst in
   * map_tree f (fun i ->
   *     subst_state_h tbl varset xlst (collect_leaves state) i
   *   ) *)
  let newsubst = List.zip_exn (collect_leaves x) (collect_leaves state) in
  List.fold ~init:f newsubst ~f:(fun acc (tmp, e1c) ->
      map_tree acc (fun bdd ->
          Bdd.compose (Bdd.topvar tmp) e1c bdd
        )
    )


