open Stdlib
module CG = CoreGrammar
open CG

let n = ref 0
let m = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let flip_id () =
  m := !m + 1;
  !m

type env = (int, (float * string option)) Hashtbl.t 

type flip = float * int list

type tree = 
  | Node of flip list * tree * tree * tree
  | Joint of tree * tree
  | Leaf of int
  | Non

let rec print_f (f: float list) = 
  match f with
  | [] -> Format.printf "";
  | head::tail -> Format.printf "%f " head; (print_f tail) 

let rec print_s (s: string list) = 
  match s with
  | [] -> Format.printf "";
  | head::tail -> Format.printf "%s " head; (print_s tail) 

let rec print_ids (ids: int list) = 
  match ids with
  | [] -> Format.printf "";
  | head::tail -> Format.printf "%d " head; (print_ids tail) 

let print_env (flip_env: env) = 
  (Hashtbl.iter (fun i (p, var) -> 
    match var with 
    | None -> Format.printf "%d -> (%f, None)\n" i p
    | Some(x) -> Format.printf "%d -> (%f, %s)\n" i p x) flip_env)

let print_string (s: string) = 
  (Format.printf "%s" s)

let nl () = 
  (Format.printf "\n";)

let round_float x =
  let d = 6 in
  let m = 10. ** (float d) in 
  (Float.floor ((x *. m) +. 0.5)) /. m

let equal f1 f2 = 
  Float.equal (round_float f1) (round_float f2)

let get_flip_ids (l: flip list) : int list = 
  let rec get_flip_ids_e (l: flip list) (ids: int list) : int list =
    match l with 
    | [] -> List.rev_append ids []
    | (_, i)::tail -> get_flip_ids_e tail (List.rev_append i ids)
  in
  get_flip_ids_e l []

(* Collect flips that need to be replaced *)
let up_pass (e: CG.expr) : tree * env =
  let flip_env = Hashtbl.create 50 in

  let rec merge l (prob, ids) new_l : flip list * flip option = 
    match l with
    | [] -> new_l, None
    | (p, i)::tail -> 
      if equal prob p then 
        (List.rev_append new_l tail), Some((p, i@ids)) 
      else 
        merge tail (prob, ids) ((p, i)::new_l)
  in
  let rec find_shared (l1: flip list) (l2: flip list) (flips: flip list) (shared: flip list)
    : flip list * flip list = 
    match l1 with
    | [] -> (List.rev_append flips l2), (List.rev_append shared [])
    | head::tail ->
      let l2', head' = merge l2 head [] in
      match head' with
      | None -> find_shared tail l2' (head::flips) shared
      | Some(h) -> find_shared tail l2' (h::flips) (h ::shared)
  in
  let rec up_pass_e (e: CG.expr) : flip list * tree =
    match e with
    | Flip(f) -> 
      let id = flip_id() in
      (Hashtbl.add flip_env id (f, None));
      [(f, [id])], Leaf(id)
    | Ite(g, thn, els) -> 
      let g_flips, g_tree = up_pass_e g in
      let thn_flips, thn_tree = up_pass_e thn in
      let els_flips, els_tree = up_pass_e els in
      let flips, shared = find_shared thn_flips els_flips [] [] in
      (g_flips@flips), Node(shared, g_tree, thn_tree, els_tree)
    | Let(_, e1, e2) | And(e1, e2) | Or(e1, e2) | Xor(e1, e2) | Eq(e1, e2) | Tup(e1, e2) ->
      let e1_flips, e1_tree = up_pass_e e1 in
      let e2_flips, e2_tree = up_pass_e e2 in
      let flips = e1_flips@e2_flips in
      flips, Joint(e1_tree, e2_tree)
    | Not(e1) -> 
      (match e1 with
      | Flip(f) -> 
        let id = flip_id() in
        (Hashtbl.add flip_env id (1.0 -. f, None));
        [(1.0 -. f, [id])], Leaf(id)
      | _ -> up_pass_e e1)
    | Snd(e1) | Fst(e1) | Observe(e1) -> up_pass_e e1
    | Ident(_) | _ -> [], Non
  in
  let _, t = up_pass_e e in
  (t, flip_env)

  (* Replace the flips with corresponding variables *)
let down_pass (e: CG.expr) (t: tree) (flip_env: env) : CG.expr = 

  let rec get_hoisted (shared: flip list) (hoisted: int list) : int list =
    match shared with
    | [] -> List.sort_uniq compare hoisted 
    | (p, ids)::tail -> 
      get_hoisted tail ((List.hd ids)::hoisted)
  in

  let rec flips_to_hoist (shared: flip list) (hoisted: int list) : int list =
    let rec create_flip (ids: int list) (entry: float * string option) : unit = 
      match ids with
      | [] -> ()
      | head::tail ->
        let curr_opt = Hashtbl.find_opt flip_env head in
        (match curr_opt with
        | None -> Hashtbl.add flip_env head entry
        | Some((p, var)) -> 
          (match var with
          | None -> Hashtbl.replace flip_env head entry
          | Some(x) -> ()));
        create_flip tail entry
    in
    match shared with
    | [] -> List.sort_uniq compare hoisted 
    | (p, ids)::tail -> 
      let x = fresh() in 
      (create_flip ids (p, Some(x)));
      flips_to_hoist tail (ids@hoisted)
  in

  let last_flip (hoisted: int list) : int option =
    let rec max (l: int list) (m: int) : int =
      match l with
      | [] -> m
      | head::tail -> 
        let m' = if m > head then m else head in
        max tail m'
    in
    match hoisted with
    | [] -> None
    | head::tail -> Some(max tail head)
  in

  let make_exprs (ids: int list) (inner: CG.expr) (rev: bool) : CG.expr = 
    let rec make_exprs_e (ids: int list) (inner: CG.expr) : CG.expr = 
      match ids with
      | [] -> inner
      | head::tail ->
        let entry = Hashtbl.find_opt flip_env head in
        match entry with
        | None -> failwith "unknown flip id"
        | Some((prob, var)) -> 
          (match var with
          | None -> failwith "missing identifier for hoisted flip"
          | Some(x) -> make_exprs_e tail (Let(x, Flip(prob), inner)))
    in
    let ids' = if rev then ids else List.rev_append ids [] in
    make_exprs_e ids' inner
  in

  let rec remove_id (hoisted: int list) (id: int) (rest: int list) : int list =
    match hoisted with
    | [] -> List.rev_append rest []
    | head::tail -> if head = id then List.rev_append rest tail else
      remove_id tail id (head::rest)
  in

  let rec down_pass_e (e: CG.expr) (t:tree) (to_hoist: int list) (hoisted: int list) (carried: int list)
    : CG.expr * int list * int list = 
    match e with
    | Flip(f) -> 
      (match to_hoist with
      | [] -> e, hoisted, carried
      | _ -> 
        (match t with
        | Leaf(id) -> 
          let entry = Hashtbl.find_opt flip_env id in
          (match entry with
          | None -> failwith "unknown flip id"
          | Some((p, var)) -> 
            (match var with
            | None -> 
              (match hoisted with
              | [] -> e, hoisted, carried
              | _ ->
                let x = fresh() in
                (Hashtbl.replace flip_env id (p, Some(x)));
                Ident(x), hoisted, (id::carried))
            | Some(x)-> 
              let hoisted' = List.sort_uniq compare (id::hoisted) in
              Ident(x), hoisted', carried))
        | _ -> failwith "unexpected flip tree element"))
    | Ite(g, thn, els) -> 
      (match t with
      | Node(shared, g_tree, thn_tree, els_tree) -> 
        let to_hoist' = flips_to_hoist shared to_hoist in
        let thn', thn_hoisted, thn_carried = down_pass_e thn thn_tree to_hoist' [] carried in
        let els', els_hoisted, els_carried = down_pass_e els els_tree to_hoist' [] thn_carried in
        let g', g_hoisted, g_carried = down_pass_e g g_tree to_hoist' [] els_carried in
        let prev_last_opt = last_flip hoisted in
        let curr_carried = 
          match prev_last_opt with
          | None -> g_carried
          | Some(last) -> List.filter (fun id -> id > last) g_carried
        in
        let prev_carried = 
          match prev_last_opt with
          | None -> []
          | Some(last) -> List.filter (fun id -> id <= last) g_carried
        in
        let curr_flips = get_hoisted shared [] in
        let curr_hoisted = List.filter (fun id -> not (List.mem id to_hoist)) curr_flips in
        let hoisted_expr = make_exprs curr_hoisted (Ite(g', thn', els')) false in
        let carried_expr = make_exprs curr_carried hoisted_expr true in
        let hoisted' = List.sort_uniq compare (hoisted@(thn_hoisted@(els_hoisted@g_hoisted))) in
        carried_expr, hoisted', prev_carried
      | _ -> failwith "unexpected flip tree element")
    | Let(x, e1, e2) -> 
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist hoisted e2_carried in
        Let(x, e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | And(e1, e2) ->
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        And(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Or(e1, e2) ->
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Or(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Xor(e1, e2) ->
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Xor(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Eq(e1, e2) ->
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Eq(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Tup(e1, e2) ->
      (match t with
      | Joint(e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Tup(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Snd(e1) -> 
      let e1', e1_hoisted, e1_carried = down_pass_e e1 t to_hoist hoisted carried in
      Snd(e1'), e1_hoisted, e1_carried
    | Fst(e1) ->
      let e1', e1_hoisted, e1_carried = down_pass_e e1 t to_hoist hoisted carried in
      Fst(e1'), e1_hoisted, e1_carried
    | Not(e1) ->
      let e1', e1_hoisted, e1_carried = down_pass_e e1 t to_hoist hoisted carried in
      Not(e1'), e1_hoisted, e1_carried
    | Observe(e1) ->
      let e1', e1_hoisted, e1_carried = down_pass_e e1 t to_hoist hoisted carried in
      Observe(e1'), e1_hoisted, e1_carried
    | Ident(_) | _ -> e, hoisted, carried
  in
  let e', _, _ = down_pass_e e t [] [] [] in
  e'

  (* Perform code motion on flip f paterns *)
let flip_code_motion (e: CG.expr) (new_n: int) : CG.expr = 
  n := new_n;
  let t, flip_env = up_pass e in
  let e' = down_pass e t flip_env in
  e'

let rec merge_branch (e: CG.expr) : CG.expr = 
  match e with
  | Flip(f) -> Flip(f)
  | Ite(g, thn, els) ->
    let n1 = merge_branch thn in
    let n2 = merge_branch els in
    (match g with
    | True -> 
      n1
    | False ->
      n2
    | _ -> 
      (match n1,n2 with
      | True, False -> g
      | False, True -> 
        (match g with
        | Flip(f) -> Flip(1.0 -. f)
        | _ -> Not(g))
      | _, _ ->
        if n1 = n2 then
          n1
        else 
          Ite(g, n1, n2)))
  | Let(v, e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Let(v, n1, n2)
  | And(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    And(n1, n2)
  | Or(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Or(n1, n2)
  | Xor(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Xor(n1, n2)
  | Eq(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Eq(n1, n2)
  | Tup(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Tup(n1, n2)  
  | Snd(e1) ->
    let n1 = merge_branch e1 in
    Snd(n1)
  | Fst(e1) ->
    let n1 = merge_branch e1 in
    Fst(n1)
  | Not(e1) ->
    let n1 = merge_branch e1 in
    Not(n1)
  | Observe(e1) ->
    let n1 = merge_branch e1 in
    Observe(n1)
  | _ -> e

let rec redundant_flip_elimination (e: CG.expr) : CG.expr =
  match e with 
  | Flip(f) ->
    if f = 0.0 then
      False
    else if f >= 1.0 then
      True
    else
      Flip(f)
  | Ite(g, thn, els) ->
    let g' = redundant_flip_elimination g in
    let n1 = redundant_flip_elimination thn in
    let n2 = redundant_flip_elimination els in
    Ite(g', n1, n2)
  | Let(v, e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    Let(v, n1, n2)
  | And(e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    And(n1, n2)
  | Or(e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    Or(n1, n2)
  | Xor(e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    Xor(n1, n2)
  | Eq(e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    Eq(n1, n2)
  | Tup(e1, e2) ->
    let n1 = redundant_flip_elimination e1 in
    let n2 = redundant_flip_elimination e2 in
    Tup(n1, n2)  
  | Snd(e1) ->
    let n1 = redundant_flip_elimination e1 in
    Snd(n1)
  | Fst(e1) ->
    let n1 = redundant_flip_elimination e1 in
    Fst(n1)
  | Not(e1) ->
    let n1 = redundant_flip_elimination e1 in
    Not(n1)
  | Observe(e1) ->
    let n1 = redundant_flip_elimination e1 in
    Observe(n1)
  | _ -> e

let do_optimize (e: CG.expr) (new_n: int) (flip_lifting: bool) (branch_elimination: bool) (determinism: bool) : CG.expr = 
  let e0 = if determinism then redundant_flip_elimination e else e in
  let e0_1 = if branch_elimination then merge_branch e0 else e0 in
  let e1 = if flip_lifting then flip_code_motion e0_1 new_n else e0_1 in 
  let e2 = if branch_elimination then merge_branch e1 else e1 in
  e2