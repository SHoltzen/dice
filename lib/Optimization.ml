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

type env = (int, (float * string option * (int * bool) list)) Hashtbl.t 

type flip = float * int list
type fact = CG.expr * int

type tree = 
  | Node of flip list * tree * tree * tree
  | Joint of flip list * tree * tree
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

let print_vals (vals: (int * bool) list) = 
  (Format.printf "{ ");
  (List.iter (fun (id, v) -> Format.printf "%d = %s, " id (if v then "T" else "F")) vals);
  (Format.printf "}\n")

let print_env (flip_env: env) = 
  (Hashtbl.iter (fun i (p, var, vals) -> 
    match var with 
    | None -> (Format.printf "%d -> (%f, None, " i p); (print_vals vals);
    | Some(x) -> (Format.printf "%d -> (%f, %s, " i p x); (print_vals vals);) flip_env)

let print_facts (facts: fact list) = 
  let rec print_facts (facts: fact list) = 
    match facts with
    | [] -> Format.printf "}\n\n";
    | (loc, id)::tail ->
      Format.printf "%s = %d\n" (CG.string_of_expr loc) id; (print_facts tail)
  in
  Format.printf "{\n";
  print_facts facts

let print_flips (flips: flip list) = 
  let rec print_flips_e (flips: flip list) =
    match flips with
    | [] -> Format.printf "\n";
    | (p, ids)::tail -> 
      Format.printf "(%f, " p; print_ids ids; Format.printf "), "; 
      print_flips_e tail
  in
  print_flips_e flips

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

let rec equal_expr e1 e2 =
  match e1 with
  | Snd(e1') -> 
    (match e2 with
    | Snd(e2') -> equal_expr e1' e2'
    | _ -> false)
  | Fst(e1') -> 
    (match e2 with
    | Fst(e2') -> equal_expr e1' e2'
    | _ -> false)
  | Ident(x) ->
    (match e2 with
    | Ident(y) -> x = y
    | _ -> false)
  | _ -> false
  
let equal_facts (loc1, id1) (loc2, id2) = 
  (equal_expr loc1 loc2) && id1 = id2

let top s =
  match s with
  | [] -> None
  | head::tail -> Some(head)

let pop s =
  match s with
  | [] -> s
  | head::tail -> tail

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
      (Hashtbl.add flip_env id (f, None, []));
      [(f, [id])], Leaf(id)
    | Ite(g, thn, els) -> 
      let g_flips, g_tree = up_pass_e g in
      let thn_flips, thn_tree = up_pass_e thn in
      let els_flips, els_tree = up_pass_e els in
      let flips, shared = find_shared thn_flips els_flips [] [] in
      (g_flips@flips), Node(shared, g_tree, thn_tree, els_tree)
    | Let(_, e1, e2) ->
      let e1_flips, e1_tree = up_pass_e e1 in
      let e2_flips, e2_tree = up_pass_e e2 in
      let flips, shared = find_shared e1_flips e2_flips [] [] in
      flips, Joint(shared, e1_tree, e2_tree)
    | And(e1, e2) | Or(e1, e2) | Xor(e1, e2) | Eq(e1, e2) | Tup(e1, e2) ->
      let e1_flips, e1_tree = up_pass_e e1 in
      let e2_flips, e2_tree = up_pass_e e2 in
      let flips = e1_flips@e2_flips in
      flips, Joint([], e1_tree, e2_tree)
    | Not(e1) -> 
      (match e1 with
      | Flip(f) -> 
        let id = flip_id() in
        (Hashtbl.add flip_env id (1.0 -. f, None, []));
        [(1.0 -. f, [id])], Leaf(id)
      | _ -> up_pass_e e1)
    | Snd(e1) | Fst(e1) | Observe(e1) -> up_pass_e e1
    | Ident(_) | _ -> [], Non
  in
  let _, t = up_pass_e e in
  (t, flip_env)

let cross_up (e: CG.expr) (t: tree) (flip_env: env) : env = 
  let merge_facts (f1: fact list) (f2: fact list) : fact list =
    List.fold_left (fun acc fact1 -> 
      if List.exists (equal_facts fact1) f2 then
        fact1::acc
      else
        acc) [] f1 
  in

  let rec x_in_loc (old_x: CG.expr) (new_x: CG.expr) (loc: CG.expr) : CG.expr option = 
    match loc with
    | Ident(_) -> if equal_expr old_x loc then Some(new_x) else None
    | Fst(e1) ->
      (match x_in_loc old_x new_x e1 with
      | None -> None
      | Some(loc') -> Some(Fst(loc')))
    | Snd(e1) ->
      (match x_in_loc old_x new_x e1 with
      | None -> None
      | Some(loc') -> Some(Snd(loc')))
    | _ -> None
  in

  let rec copy_facts (old_x: CG.expr) (new_x: CG.expr) (facts: fact list) (acc: fact list) : fact list =
    match facts with
    | [] -> List.rev_append acc []
    | (loc, id)::tail ->
      (match x_in_loc old_x new_x loc with
      | None -> copy_facts old_x new_x tail ((loc, id)::acc)
      | Some(loc') -> copy_facts old_x new_x tail ((loc', id)::((loc, id)::acc)))
  in

  let rec remove_facts (x: CG.expr) (facts: fact list) (acc: fact list) : fact list =
    match facts with
    | [] -> List.rev_append acc []
    | (loc, id)::tail ->
      if equal_expr loc x then remove_facts x tail acc else remove_facts x tail ((loc, id)::acc)
  in

  let flip_vals (old_vals: (int * bool) list) (new_vals: (int * bool) list) : (int * bool) list =
    List.filter_map (fun (id1, v1) -> 
      if List.exists (fun (id2, _) -> id1 = id2) old_vals then
        Some(id1, v1)
      else
        Some(id1, not v1)) new_vals
  in

  let rec cross_up_guard (e: CG.expr) (t: tree) (facts: fact list) (x_stack: CG.expr list) 
    (vals_thn: (int * bool) list) (vals_els: (int * bool) list)
   : fact list * (int * bool) list * (int * bool) list = 
    match e with
    | Let(x, e1, e2) ->
      (match t with 
      | Joint(_, e1_tree, e2_tree) -> 
        let e1_facts, _, _ = cross_up_guard e1 e1_tree facts (Ident(x)::x_stack) vals_thn vals_els in
        let e2_facts, e2_vals_thn, e2_vals_els = cross_up_guard e2 e2_tree e1_facts x_stack vals_thn vals_els in
        let facts' = remove_facts (Ident(x)) e2_facts [] in
        facts', e2_vals_thn, e2_vals_els
      | _ -> failwith "unexpected flip tree element")
    | Ite(g, thn, els) ->
      (match t with
      | Node(_, g_tree, thn_tree, els_tree) ->
        let g_facts, g_vals_thn, g_vals_els = cross_up_guard g g_tree facts x_stack vals_thn vals_thn in
        let thn_facts, _, _ = cross_up_guard thn thn_tree facts x_stack g_vals_thn g_vals_thn in
        let els_facts, _, _ = cross_up_guard els els_tree facts x_stack g_vals_els g_vals_els in
        let facts' = merge_facts thn_facts els_facts in
        facts', vals_thn, vals_els
      | _ -> failwith "unexpected flip tree element")
    | Ident(x) ->
      let left_x_opt = top x_stack in
      let facts'' = 
        match left_x_opt with
        | None -> facts
        | Some(left_x) -> 
          let facts' = copy_facts (Ident(x)) left_x facts [] in
          facts'
      in
      let vals_thn', vals_els' = 
        List.fold_left (fun (thn, els) (loc, id) -> 
          if equal_expr (Ident(x)) loc then
            (id, true)::thn, (id, false)::els
          else
            thn, els) (vals_thn, vals_els) facts'' 
      in
      facts'', vals_thn', vals_els'
    | Flip(f) ->
      (match t with
      | Leaf(id) -> 
        let facts' = 
          let left_x_opt = top x_stack in
          match left_x_opt with
          | None -> facts
          | Some(left_x) -> (left_x, id)::facts
        in
        let entry_opt = Hashtbl.find_opt flip_env id in
        (match entry_opt with
        | None -> failwith "can't find flip entry"
        | Some(p, x, v) -> (Hashtbl.replace flip_env id (p, x, (vals_thn@v))););
        let vals_thn' = (id, true)::vals_thn in
        let vals_els' = (id, false)::vals_els in
        facts', vals_thn', vals_els'
      | _ -> failwith "unexpected flip tree element")
    | Tup(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let left_x_opt = top x_stack in
        (match left_x_opt with
        | None -> facts, vals_thn, vals_els
        | Some(left_x) -> 
          let x_stack_tail = pop x_stack in
          let e1_facts, e1_vals_thn, e1_vals_els = cross_up_guard e1 e1_tree facts 
            (Fst(left_x)::x_stack_tail) vals_thn vals_els in
          let e2_facts, e2_vals_thn, e2_vals_els = cross_up_guard e2 e2_tree e1_facts 
            (Snd(left_x)::x_stack_tail) e1_vals_thn e1_vals_els in
          e2_facts, e2_vals_thn, e2_vals_els)
      | _ -> failwith "unexpected flip tree element")
    | And(e1, e2) | Eq(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e1_facts, e1_vals_thn, _ = cross_up_guard e1 e1_tree facts x_stack 
          vals_thn vals_els in
        let e2_facts, e2_vals_thn, _ = cross_up_guard e2 e2_tree e1_facts x_stack 
          e1_vals_thn vals_els in
        e2_facts, e2_vals_thn, vals_els
      | _ -> failwith "unexpected flip tree element")
    | Or(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e1_facts, _, e1_vals_els = cross_up_guard e1 e1_tree facts x_stack 
          vals_thn vals_els in
        let e2_facts, _, e2_vals_els = cross_up_guard e2 e2_tree e1_facts x_stack 
          vals_thn e1_vals_els in
        e2_facts, vals_thn, e2_vals_els
      | _ -> failwith "unexpected flip tree element")
    | Xor(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e1_facts, _, _ = cross_up_guard e1 e1_tree facts x_stack 
          vals_thn vals_els in
        let e2_facts, _, _ = cross_up_guard e2 e2_tree e1_facts x_stack 
          vals_thn vals_els in
        e2_facts, vals_thn, vals_els
      | _ -> failwith "unexpected flip tree element")
    | Not(e1) -> 
      (match e1 with
      | Ident(x) ->
        let left_x_opt = top x_stack in
        let facts'' = 
          match left_x_opt with
          | None -> facts
          | Some(left_x) -> 
            let facts' = copy_facts (Ident(x)) left_x facts [] in
            facts'
        in
        let vals_thn', vals_els' = 
          List.fold_left (fun (vals_thn, vals_els) (loc, id) -> 
            if equal_expr (Ident(x)) loc then
              (id, false)::vals_thn, (id, true)::vals_els
            else
              vals_thn, vals_els) (vals_thn, vals_els) facts'' 
        in
        facts'', vals_thn', vals_els'
      | _ -> 
        let e1_facts, _, _ = cross_up_guard e1 t facts x_stack vals_thn vals_els in
        e1_facts, vals_thn, vals_els)
    | Snd(e1) | Fst(e1) ->
      let vals_thn', vals_els' = 
        List.fold_left (fun (vals_thn, vals_els) (loc, id) -> 
          if equal_expr e loc then
            (id, true)::vals_thn, (id, false)::vals_els
          else
            vals_thn, vals_els) (vals_thn, vals_els) facts
      in
      let e1_facts, e1_vals_thn, e1_vals_els = cross_up_guard e1 t facts x_stack vals_thn' vals_els' in
      e1_facts, e1_vals_thn, e1_vals_els    
    | Observe(e1) ->
      let e1_facts, e1_vals_thn, e1_vals_els = cross_up_guard e1 t facts x_stack vals_thn vals_els in
      e1_facts, e1_vals_thn, e1_vals_els
    | _ -> facts, vals_thn, vals_els
  in

  let rec cross_up_e (e: CG.expr) (t: tree) (facts: fact list) (x_stack: CG.expr list) (vals: (int * bool) list)
   : fact list * (int * bool) list =
    match e with
    | Let(x, e1, e2) ->
      (match t with 
      | Joint(_, e1_tree, e2_tree) -> 
        let e1_facts, _ = cross_up_e e1 e1_tree facts (Ident(x)::x_stack) vals in
        let e2_facts, e2_vals = cross_up_e e2 e2_tree e1_facts x_stack vals in
        let facts' = remove_facts (Ident(x)) e2_facts [] in
        facts', e2_vals
      | _ -> failwith "unexpected flip tree element")
    | Ite(g, thn, els) ->
      (match t with
      | Node(_, g_tree, thn_tree, els_tree) ->
        let g_facts, g_vals_thn, g_vals_els = cross_up_guard g g_tree facts x_stack vals vals in
        let thn_facts, _ = cross_up_e thn thn_tree facts x_stack g_vals_thn in
        let els_facts, _ = cross_up_e els els_tree facts x_stack g_vals_els in
        let facts' = merge_facts thn_facts els_facts in
        facts', vals
      | _ -> failwith "unexpected flip tree element")
    | Ident(x) ->
      let left_x_opt = top x_stack in
      let facts'' = 
        match left_x_opt with
        | None -> facts
        | Some(left_x) -> 
          let facts' = copy_facts (Ident(x)) left_x facts [] in
          facts'
      in
      let vals' = 
        List.fold_left (fun acc (loc, id) -> 
          if equal_expr (Ident(x)) loc then
            (id, true)::acc
          else
            acc) vals facts'' 
      in
      facts'', vals'
    | Flip(f) ->
      (match t with
      | Leaf(id) -> 
        let facts' = 
          let left_x_opt = top x_stack in
          match left_x_opt with
          | None -> facts
          | Some(left_x) -> (left_x, id)::facts
        in
        let entry_opt = Hashtbl.find_opt flip_env id in
        (match entry_opt with
        | None -> failwith "can't find flip entry"
        | Some(p, x, v) -> (Hashtbl.replace flip_env id (p, x, (vals@v))););
        let vals' = (id, true)::vals in
        facts', vals'
      | _ -> failwith "unexpected flip tree element")
    | Tup(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let left_x_opt = top x_stack in
        (match left_x_opt with
        | None -> facts, vals
        | Some(left_x) -> 
          let x_stack_tail = pop x_stack in
          let e1_facts, e1_vals = cross_up_e e1 e1_tree facts (Fst(left_x)::x_stack_tail) vals in
          let e2_facts, e2_vals = cross_up_e e2 e2_tree e1_facts (Snd(left_x)::x_stack_tail) e1_vals in
          e2_facts, e2_vals)
      | _ -> failwith "unexpected flip tree element")
    | And(e1, e2) | Or(e1, e2) | Xor(e1, e2) | Eq(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e1_facts, e1_vals = cross_up_e e1 e1_tree facts x_stack vals in
        let e2_facts, e2_vals = cross_up_e e2 e2_tree e1_facts x_stack e1_vals in
        e2_facts, e2_vals
      | _ -> failwith "unexpected flip tree element")
    | Not(e1) -> 
      (match e1 with
      | Ident(x) ->
        let left_x_opt = top x_stack in
        let facts'' = 
          match left_x_opt with
          | None -> facts
          | Some(left_x) -> 
            let facts' = copy_facts (Ident(x)) left_x facts [] in
            facts'
        in
        let vals' = 
          List.fold_left (fun acc (loc, id) -> 
            if equal_expr (Ident(x)) loc then
              (id, false)::acc
            else
              acc) vals facts'' 
        in
        facts'', vals'
      | _ -> 
        let e1_facts, e1_vals = cross_up_e e1 t facts x_stack vals in
        e1_facts, vals)
    | Snd(e1) | Fst(e1) ->
      let vals' = 
        List.fold_left (fun acc (loc, id) -> 
          if equal_expr e loc then
            (id, true)::acc
          else
            acc) vals facts 
      in
      let e1_facts, e1_vals = cross_up_e e1 t facts x_stack vals' in
      e1_facts, e1_vals    
    | Observe(e1) ->
      let e1_facts, e1_vals = cross_up_e e1 t facts x_stack vals in
      e1_facts, e1_vals
    | _ -> facts, vals
  in
  let facts, vals = cross_up_e e t [] [] [] in
  flip_env

  (* Replace the flips with corresponding variables *)
let down_pass (e: CG.expr) (t: tree) (flip_env: env) : CG.expr = 

  let get_hoisted (shared: flip list) (to_hoist: int list) (to_hoist': int list) : int list =
    let rec get_hoisted_e (shared: flip list) (hoisted: int list) : int list =
      match shared with
      | [] -> List.sort_uniq compare hoisted 
      | (p, ids)::tail -> 
        let ids' = List.filter (fun id -> not (List.mem id to_hoist) && (List.mem id to_hoist')) ids in
        (match ids' with
        | [] -> get_hoisted_e tail hoisted
        | head::_ -> get_hoisted_e tail (head::hoisted))
    in
    get_hoisted_e shared []
  in

  let rec flips_to_hoist (shared: flip list) (hoisted: int list) (curr_flips: int list) : int list * int list =
    let rec find_hoisted_var (ids: int list) : string option = 
      match ids with
      | [] -> None
      | head::tail ->         
        let entry_opt = Hashtbl.find_opt flip_env head in
        (match entry_opt with
        | None -> failwith "cannot find flip with flip id"
        | Some((_, var, _)) -> 
          (match var with
          | None -> find_hoisted_var tail
          | Some(x) -> Some(x)))
    in
    let rec create_flip (ids: int list) (entry: float * string option * (int * bool) list) : unit = 
      match ids with
      | [] -> ()
      | head::tail ->
        let curr_opt = Hashtbl.find_opt flip_env head in
        (match curr_opt with
        | None -> failwith "cannot find flip with flip id"
        | Some((p, var, vals)) -> 
          (match var with
          | None -> Hashtbl.replace flip_env head entry
          | Some(x) -> ()));
        create_flip tail entry
    in
    match shared with
    | [] -> (List.sort_uniq compare hoisted), curr_flips
    | (p, ids)::tail -> 
      let x, curr_flips' = 
        match find_hoisted_var ids with
        | None -> fresh(), ((List.hd ids)::curr_flips)
        | Some(x) -> x, curr_flips
      in 
      (create_flip ids (p, Some(x), []));
      flips_to_hoist tail (ids@hoisted) curr_flips'
  in

  let rec cross_flips_to_hoist (shared: flip list) (hoisted: int list) (curr_flips: int list) : int list * int list = 
    let create_flip (ids: int list) (p: float) (hoisted: int list) (curr_flips: int list) : int list * int list = 
      let check_flips (id: int) (prev: int list) (hoisted: int list) (curr_flips: int list) : int list * int list = 
        let check_facts (vals1: (int * bool) list) (vals2: (int * bool) list) : bool =
          List.fold_left (fun acc (id1, v1) ->
            List.fold_left (fun acc (id2, v2) -> 
              if id1 = id2 && not v1 = v2 then
                true
              else
                acc
              ) acc vals2
            ) false vals1
        in
        let rec match_var (p1, var1, vals1) (prev: int list) (hoisted: int list) (curr_flips: int list) : int list * int list =
          match prev with
          | [] -> hoisted, curr_flips
          | id2::tail ->
            let id2_entry_opt = Hashtbl.find_opt flip_env id2 in
            (match id2_entry_opt with
            | None -> failwith "cannot find flip with flip id"
            | Some((p2, var2, vals2)) -> 
              if check_facts vals1 vals2 then
                let hoisted' = (id::(id2::hoisted)) in
                let curr_flips' = 
                  (match var2 with
                  | None -> 
                    let x = fresh() in
                    (Hashtbl.replace flip_env id (p1, Some(x), vals1));
                    (Hashtbl.replace flip_env id2 (p2, Some(x), vals2));
                    (id2::curr_flips)
                  | Some(x) ->
                    (Hashtbl.replace flip_env id (p1, Some(x), vals1));
                    curr_flips)
                in
                hoisted', curr_flips'
              else
                match_var (p1, var1, vals1) tail hoisted curr_flips)
        in
        let id1_entry_opt = Hashtbl.find_opt flip_env id in
        (match id1_entry_opt with
        | None -> failwith "cannot find flip with flip id"
        | Some(entry) ->
          match_var entry prev hoisted curr_flips)
      in
      let hoisted', curr_flips', _ = List.fold_left (fun (hoisted, curr_flips, prev) id -> 
        let hoisted', curr_flips' = check_flips id prev hoisted curr_flips in
        let prev' = id::prev in
        hoisted', curr_flips', prev') (hoisted, curr_flips, []) ids in
      hoisted', curr_flips'
    in
    match shared with
    | [] -> 
      let hoisted' = List.sort_uniq compare hoisted in
      hoisted', curr_flips
    | (p, ids)::tail -> 
      let hoisted', curr_flips' = create_flip ids p hoisted curr_flips in
      cross_flips_to_hoist tail hoisted' curr_flips'
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

  let make_exprs (ids: int list) (inner: CG.expr) : CG.expr = 
    let rec make_exprs_e (ids: int list) (inner: CG.expr) : CG.expr = 
      match ids with
      | [] -> inner
      | head::tail ->
        let entry = Hashtbl.find_opt flip_env head in
        match entry with
        | None -> failwith "unknown flip id"
        | Some((prob, var, vals)) -> 
          (match var with
          | None -> failwith "missing identifier for hoisted flip"
          | Some(x) -> 
          make_exprs_e tail (Let(x, Flip(prob), inner)))
    in
    let ids' = List.rev_append ids [] in
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
          | Some((p, var, vals)) -> 
            (match var with
            | None -> 
              let last_opt = last_flip to_hoist in
              (match last_opt with
              | None -> e, hoisted, carried
              | Some(last) ->
                if id < last then
                  let x = fresh() in
                  Hashtbl.replace flip_env id (p, Some(x), vals);
                  Ident(x), hoisted, (id::carried)
                else
                  e, hoisted, carried)
            | Some(x)-> 
              let hoisted' = List.sort_uniq compare (id::hoisted) in
              Ident(x), hoisted', carried))
        | _ -> failwith "unexpected flip tree element"))
    | Ite(g, thn, els) -> 
      (match t with
      | Node(shared, g_tree, thn_tree, els_tree) -> 
        let to_hoist', curr_hoisted = flips_to_hoist shared to_hoist [] in
        let thn', thn_hoisted, thn_carried = down_pass_e thn thn_tree to_hoist' [] carried in
        let els', els_hoisted, els_carried = down_pass_e els els_tree to_hoist' thn_hoisted thn_carried in
        let g', g_hoisted, g_carried = down_pass_e g g_tree to_hoist' els_hoisted els_carried in

        let prev_last_opt = last_flip to_hoist in

        let all_flips = List.rev_append curr_hoisted g_carried
          |> List.sort_uniq compare in

        let curr_flips = 
          match prev_last_opt with
          | None -> all_flips
          | Some(last) -> List.filter (fun id -> id > last) all_flips
        in
        let prev_flips = 
          match prev_last_opt with
          | None -> []
          | Some(last) -> List.filter (fun id -> id <= last) all_flips
        in

        let hoisted_expr = make_exprs curr_flips (Ite(g', thn', els')) in
        let hoisted' = List.sort_uniq compare (hoisted@g_hoisted) in
        hoisted_expr, hoisted', prev_flips
      | _ -> failwith "unexpected flip tree element")
    | Let(x, e1, e2) -> 
      (match t with
      | Joint(shared, e1_tree, e2_tree) -> 
        let to_hoist', curr_hoisted = cross_flips_to_hoist shared to_hoist [] in
        
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist' hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist' e2_hoisted e2_carried in

        let prev_last_opt = last_flip to_hoist in

        let all_flips = List.rev_append curr_hoisted e1_carried
          |> List.sort_uniq compare in

        let curr_flips = 
          match prev_last_opt with
          | None -> all_flips
          | Some(last) -> List.filter (fun id -> id > last) all_flips
        in
        let prev_flips = 
          match prev_last_opt with
          | None -> []
          | Some(last) -> List.filter (fun id -> id <= last) all_flips
        in

        let hoisted_expr = make_exprs curr_flips (Let(x, e1', e2')) in
        
        let hoisted' = List.sort_uniq compare (hoisted@e1_hoisted) in
        hoisted_expr, hoisted', prev_flips
      | _ -> failwith "unexpected flip tree element")
    | And(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        And(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Or(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Or(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Xor(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Xor(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Eq(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
        let e2', e2_hoisted, e2_carried = down_pass_e e2 e2_tree to_hoist hoisted carried in
        let e1', e1_hoisted, e1_carried = down_pass_e e1 e1_tree to_hoist e2_hoisted e2_carried in
        Eq(e1', e2'), e1_hoisted, e1_carried
      | _ -> failwith "unexpected flip tree element")
    | Tup(e1, e2) ->
      (match t with
      | Joint(_, e1_tree, e2_tree) ->
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
let do_flip_hoisting (e: CG.expr) (new_n: int) (cross_table: bool) : CG.expr = 
  n := new_n;
  let t, flip_env = up_pass e in
  let flip_env' = if cross_table then cross_up e t flip_env else flip_env in
  let e' = down_pass e t flip_env' in
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

let do_optimize (e: CG.expr) (new_n: int) (flip_hoisting: bool) (cross_table: bool) (branch_elimination: bool) (determinism: bool) : CG.expr = 
  let e0 = if determinism then redundant_flip_elimination e else e in
  let e0_1 = if branch_elimination then merge_branch e0 else e0 in
  let e1 = if flip_hoisting then do_flip_hoisting e0_1 new_n cross_table else e0_1 in 
  let e2 = if branch_elimination then merge_branch e1 else e1 in
  e2