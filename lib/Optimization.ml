open Stdlib
module CG = CoreGrammar
module StringMap = Map.Make(String)
open CG

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

type tracker_entry = (bool * bool * float * string * string list)
type tracker = tracker_entry list
type env = CG.expr StringMap.t

let rec print_f (f: float list) = 
  match f with
  | [] -> Format.printf "";
  | head::tail -> Format.printf "%f " head; (print_f tail) 

let rec print_s (s: string list) = 
  match s with
  | [] -> Format.printf "";
  | head::tail -> Format.printf "%s " head; (print_s tail) 

let rec print_tracker (flip_to_var: tracker) = 
  match flip_to_var with
  | [] -> Format.printf "";
  | (used, new_flip, f, v, s)::tail ->
    let u = if used then "used" else "not used" in
    let n = if new_flip then "new" else "old" in
    Format.printf "(%s, %s, %f, %s, [" u n f v ;
    print_s s;
    Format.printf "]) ";
    print_tracker tail

let print_string (s: string) = 
  (Format.printf "%s" s)

let newline () = 
  (Format.printf "\n";)

type tree = 
  | Node of (float list * float list) * tree * tree
  | Branch of float list * tree * tree
  | Leaf 

let rec remove_one l f new_l = 
  match l with
  | [] -> new_l, false
  | head::tail -> if f head then (List.rev_append new_l tail), true else 
    remove_one tail f (head::new_l)

let rec replace l x new_x new_l = 
  match l with
  | [] -> new_l, false
  | head::tail -> if head = x then (List.rev_append new_l (new_x::tail)), true else 
    replace tail x new_x (head::new_l)

(* Collect flips that need to be replaced *)
let rec up_pass (e: CG.expr) : float list * tree  =
  let rec find_shared (l1: float list) (l2: float list) (flips: float list) (shared: float list)
    : float list * float list = 
    match l1 with
    | [] -> (List.rev_append flips l2), (List.rev_append shared [])
    | head::tail ->
      let new_l2, did_remove = remove_one l2 (fun x -> x = head) [] in
      if did_remove then
        find_shared tail new_l2 (head::flips) (head::shared)
      else
        find_shared tail new_l2 (head::flips) shared
  in

  match e with
  | Flip(f) -> [f], Leaf
  | Ite(g, thn, els) -> 
    (* let g_flips, _ = up_pass g in *)

    let thn_flips, thn_tree = up_pass thn in
    let els_flips, els_tree = up_pass els in
    let flips, shared = find_shared thn_flips els_flips [] [] in
    flips, Node((flips, shared), thn_tree, els_tree)
  | Let(_, e1, e2) -> 
    let e1_flips, e1_tree = up_pass e1 in
    let e2_flips, e2_tree = up_pass e2 in
    e1_flips@e2_flips, Branch(e1_flips, e1_tree, e2_tree)
  | And(e1, e2) | Or(e1, e2) | Xor(e1, e2) | Eq(e1, e2) | Tup(e1, e2) ->
    let e1_flips, _ = up_pass e1 in
    let e2_flips, _ = up_pass e2 in
    let flips = e1_flips@e2_flips in
    flips, Leaf
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> up_pass e1
  | Ident(_) | _ -> [], Leaf

  (* Replace the flips with corresponding variables *)
let down_pass (e: CG.expr) (t: tree) : CG.expr = 
  let rec get_var (flip_to_var_head: tracker) (flip_to_var: tracker) (flip: float) : string option * tracker = 
    match flip_to_var with
    | [] -> None, (List.rev_append flip_to_var [])
    | (used, new_flip, f, var, s)::tail -> 
      if not used && f = flip then
        Some(var), (List.rev_append flip_to_var_head ((true, new_flip, f, var, s)::tail))
      else
        get_var ((used, new_flip, f, var, s)::flip_to_var_head) tail flip
  in

  let rec need_to_lift (flip_to_var: tracker) (flips: float list) : bool =
    let rec need_to_lift_e (flip_to_var: tracker) (flip: float) : bool = 
      match flip_to_var with
      | [] -> false
      | (used, _, f, _, _)::tail ->
        if not used && f = flip then
          true
        else
          need_to_lift_e tail flip
    in
    match flips with
    | [] -> false
    | flip::tail ->
      let res = need_to_lift_e flip_to_var flip in
      if res then
        true
      else
        need_to_lift flip_to_var tail
  in

  let rec lift_new_flip (flip_to_var_temp: tracker) (flip_to_var: tracker) (var_to_expr: env) (flips: float list)
    : tracker * env  =
    let rec check_if_exist (flip_to_var_head: tracker) (flip_to_var: tracker) (flip: float) : bool * tracker = 
      match flip_to_var with
      | [] -> false, []
      | (used, new_flip, f, var, s)::tail -> 
        if f = flip then
          true, (List.rev_append flip_to_var_head tail)
        else
          check_if_exist ((used, new_flip, f, var, s)::flip_to_var_head) tail flip
    in
    match flips with
    | [] -> flip_to_var, var_to_expr
    | flip::tail ->
      let flip_exists, flip_to_var_temp' = check_if_exist [] flip_to_var_temp flip in
      if flip_exists then
        lift_new_flip flip_to_var_temp' flip_to_var var_to_expr tail
      else
        let var = fresh() in
        lift_new_flip (flip_to_var) ((false, true, flip, var, [])::flip_to_var) (StringMap.add var (Flip(flip)) var_to_expr) tail
  in
  
  let rec is_var_lifted (flip_to_var: tracker) (var: string) : bool = 
    match flip_to_var with
    | [] -> false
    | (_, _, _, v, _)::tail -> 
      if v = var then
        true
      else
        is_var_lifted tail var
  in

  let rec is_var_squeezed (flip_to_var: tracker) (var: string) : bool = 
    match flip_to_var with
    | [] -> false
    | (_,_, _, _, s)::tail -> 
      if (List.mem var s) then
        true
      else
        is_var_squeezed tail var
  in

  let rec remove_lifted (flip_to_var_head: tracker) (flip_to_var: tracker) : tracker = 
    let rec update_if_squeezed (flip_to_var: tracker) (x: string) (squeezed: string list) : bool * tracker = 
      let rec insert_squeezed (s_head: string list) (s: string list) (x: string) (squeezed: string list): bool * string list = 
        match s with
        | [] -> false, (List.rev_append s_head [])
        | head::tail -> 
          if head = x then
            true, (List.rev_append (List.rev_append s_head squeezed) s)
          else
            insert_squeezed (head::s_head) tail x squeezed
      in
      match flip_to_var with
      | [] -> false, flip_to_var
      | (used, new_flip, f, var, s)::tail ->
        let squeezed_already, tail' = update_if_squeezed tail x squeezed in
        if squeezed_already then
          true, ((used, new_flip, f, var, s)::tail')
        else
          let inserted, s' = insert_squeezed [] s x squeezed in
          if inserted then
            true, ((used, new_flip, f, var, s')::tail)
          else
            false, ((used, new_flip, f, var, s)::tail)
    in
    let rec remove_if_already_squeezed (flip_to_var: tracker) (s: string list) (new_s: string list): string list = 
      match s with
      | [] -> List.rev_append new_s []
      | head::tail ->
        if is_var_squeezed flip_to_var head then
          remove_if_already_squeezed flip_to_var tail new_s
        else
          remove_if_already_squeezed flip_to_var tail (head::new_s)
    in
    let rec remove_if_already_lifted (flip_to_var_head: tracker) (flip_to_var: tracker) (x: string) (did_remove: bool): bool * tracker = 
      let rec remove_if_already_lifted_e (s_head: string list) (s: string list) (x: string) (did_remove: bool) : bool * string list =
        match s with
        | [] -> did_remove, List.rev_append s_head []
        | head::tail -> 
          if head = x then
            remove_if_already_lifted_e s_head tail x true
          else
            remove_if_already_lifted_e (head::s_head) tail x did_remove
      in
      match flip_to_var with
      | [] -> did_remove, List.rev_append flip_to_var_head []
      | (used, new_flip, f, var, s)::tail ->
        let did_remove', s' = remove_if_already_lifted_e [] s x did_remove in
        remove_if_already_lifted ((used, new_flip, f, var, s')::flip_to_var_head) tail x did_remove'
    in
    match flip_to_var with
    | [] -> List.rev_append flip_to_var_head []
    | (used, new_flip, f, var, s)::tail ->
      let s' = remove_if_already_squeezed tail s [] in
      let is_squeezed_tail, tail' = update_if_squeezed tail var s' in
      if is_squeezed_tail then
        remove_lifted flip_to_var_head tail'
      else 
        let did_remove, flip_to_var_head' = remove_if_already_lifted [] flip_to_var_head var false in
        remove_lifted (((used||did_remove),new_flip,f,var,s')::flip_to_var_head') tail
  in

  let rec lift_ident (flip_to_var: tracker) (x: string) (flips_to_check: float list) (squeezed_s: string list)
    : bool * bool * tracker = 
    match flip_to_var with
    | [] -> false, false, []
    | (used, new_flip, f, var, s)::tail ->
      let in_upper_level, is_lifted, tail' = lift_ident tail x flips_to_check squeezed_s in
      if in_upper_level then
        true, is_lifted, ((used,new_flip,f,var,s)::tail')
      else if List.mem x s then
        true, false, flip_to_var
      else if List.mem f flips_to_check then
        true, true, ((used, new_flip, f, var, ((x::squeezed_s)@s))::tail)
      else
        false, false, flip_to_var
  in

  let rec concatenate_squeezed_exprs (flip_to_var_head: tracker) (flip_to_var_thn: tracker) (flip_to_var_els: tracker) (var_to_expr: env) (els: CG.expr): tracker * env * CG.expr = 
    let rec concatenate_squeezed_exprs_e (flip_to_var_entry: tracker_entry) (flip_to_var_thn_tail: tracker) (flip_to_var_els_head: tracker) (flip_to_var_els: tracker) (var_to_expr: env) (inner: CG.expr)
     : tracker_entry * tracker * env * CG.expr = 
      let rec merge_s (s1: string list) (s2: string list) (s_merge: string list): string list = 
        match s1 with
        | [] -> List.rev_append s_merge s2
        | head::tail ->
          if List.mem head s2 then
            merge_s tail s2 s_merge
          else
            merge_s tail s2 (head::s_merge)
      in
      let rec replace_expr (e: CG.expr) (var: string) (new_var: string) (flip_var: string): bool * CG.expr =
        let rec replace_expr_search_dependency (e: CG.expr) (flip_var: string): bool * CG.expr = 
          match e with
          | Ident(x) -> (x = flip_var), e
          | Let(x, e1, e2) ->
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            let did_replace, e1' = if is_dep_e2 then replace_dependent_var e1 var new_var else false, e1 in
            let is_dep_e1, e1'' = replace_expr_search_dependency e1' flip_var in
            (is_dep_e1 || is_dep_e2), Let(x, e1'', e2')
          | Ite(g, thn, els) ->
            let is_dep_thn, thn' = replace_expr_search_dependency thn flip_var in
            let is_dep_els, els' = replace_expr_search_dependency els flip_var in
            let g' = 
              if is_dep_thn || is_dep_els then
                let did_replace, g_replaced = replace_dependent_var g var new_var in
                g_replaced
              else
                g
            in
            (is_dep_thn || is_dep_els), Ite(g', thn', els')
          | And(e1, e2) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            (is_dep_e1 || is_dep_e2), And(e1', e2')
          | Or(e1, e2) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            (is_dep_e1 || is_dep_e2), Or(e1', e2')
          | Xor(e1, e2) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            (is_dep_e1 || is_dep_e2), Xor(e1', e2')
          | Eq(e1, e2) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            (is_dep_e1 || is_dep_e2), Eq(e1', e2')
          | Tup(e1, e2) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            let is_dep_e2, e2' = replace_expr_search_dependency e2 flip_var in
            (is_dep_e1 || is_dep_e2), Tup(e1', e2')
          | Snd(e1) -> 
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            is_dep_e1, Snd(e1')
          | Fst(e1) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            is_dep_e1, Fst(e1')
          | Not(e1) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            is_dep_e1, Not(e1')
          | Observe(e1) ->
            let is_dep_e1, e1' = replace_expr_search_dependency e1 flip_var in
            is_dep_e1, Observe(e1')
          | _ -> false, e
        and replace_dependent_var (e: CG.expr) (var: string) (new_var: string): bool * CG.expr =
          match e with
          | Ident(x) -> if x = var then true, Ident(new_var) else false, e
          | Let(x, e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), Let(x, e1', e2')
          | Ite(g, e1, e2) ->
            let did_replace_g, g' = replace_dependent_var g var new_var in
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_g || did_replace_e1 || did_replace_e2), Ite(g', e1', e2')
          | And(e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), And(e1', e2')
          | Or(e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), Or(e1', e2')
          | Xor(e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), Xor(e1', e2')
          | Eq(e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), Eq(e1', e2')
          | Tup(e1, e2) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            let did_replace_e2, e2' = replace_dependent_var e2 var new_var in
            (did_replace_e1 || did_replace_e2), Tup(e1', e2')
          | Snd(e1) -> 
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            did_replace_e1, Snd(e1')
          | Fst(e1) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            did_replace_e1, Fst(e1')
          | Not(e1) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            did_replace_e1, Not(e1')
          | Observe(e1) ->
            let did_replace_e1, e1' = replace_dependent_var e1 var new_var in
            did_replace_e1, Observe(e1')
          | _ -> false, e
        in
        replace_expr_search_dependency e flip_var 
      in
      match flip_to_var_els with
      | [] -> flip_to_var_entry, (List.rev_append flip_to_var_els_head []), var_to_expr, inner
      | (used, new_flip, f, var, s)::tail ->
        let used', new_flip', f', var', s' = flip_to_var_entry in
        if List.mem var' s && (List.mem var s' || is_var_lifted flip_to_var_thn_tail var) then
          let new_ident = fresh() in
          let var_to_expr' = StringMap.add new_ident (StringMap.find var' var_to_expr) var_to_expr in

          let s_replaced, did_replace = replace s var' new_ident [] in
          let did_replace, inner' = replace_expr inner var' new_ident var in 

          concatenate_squeezed_exprs_e flip_to_var_entry flip_to_var_thn_tail ((used, new_flip, f, var, s_replaced)::flip_to_var_els_head) tail var_to_expr' inner'
        else
          if var = var' && f = f' then
            ((used || used'), (new_flip && new_flip'), f', var', (merge_s s' s [])), (List.rev_append flip_to_var_els_head tail), var_to_expr, inner
          else
            concatenate_squeezed_exprs_e flip_to_var_entry flip_to_var_thn_tail ((used, new_flip, f, var, s)::flip_to_var_els_head) tail var_to_expr inner
    in
    match flip_to_var_thn with
    | [] -> (List.rev_append (List.rev_append flip_to_var_els []) (List.rev_append flip_to_var_head [])), var_to_expr, els
    | head::tail ->
      let head', flip_to_var_els', var_to_expr', els' = concatenate_squeezed_exprs_e head tail [] flip_to_var_els var_to_expr els in
      concatenate_squeezed_exprs (head'::flip_to_var_head) tail flip_to_var_els' var_to_expr' els'
  in

  let rec make_expression (flip_to_var: tracker) (var_to_expr: env) (inner: CG.expr) : CG.expr =
    let rec make_squeezed (s: string list) (inner: CG.expr) : CG.expr = 
      let rec rec_check_var_exists (e: CG.expr) (var: string) : bool =
        match e with
        | Ident(x) -> x = var
        | Flip(_) -> false
        | Ite(g1, e1, e2) ->
          (rec_check_var_exists g1 var) || (rec_check_var_exists e1 var) || (rec_check_var_exists e2 var)
        | And(e1, e2) | Or(e1, e2) | Xor(e1, e2) | Eq(e1, e2) | Tup(e1, e2) ->
          (rec_check_var_exists e1 var) || (rec_check_var_exists e2 var)
        | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> 
          (rec_check_var_exists e1 var)
        | _ -> false
      in
      match s with
      | [] -> inner
      | var::tail ->
        let expr = 
          match StringMap.find_opt var var_to_expr with
          | None -> failwith "can't find var to make"
          | Some(e) -> 
            let var_still_exists = StringMap.exists (fun _ e1 -> rec_check_var_exists e1 var) var_to_expr in
            if var_still_exists then
              inner
            else
              Let(var, e, inner) 
        in
        make_squeezed tail expr
    in
    match flip_to_var with
    | [] -> inner
    | (used, new_flip, f, var, s)::tail -> 
      if new_flip then
        let expr = make_squeezed s (Let(var, Flip(f), inner)) in
        make_expression tail var_to_expr expr 
      else
        make_expression tail var_to_expr inner 
  in

  let rec clean_bookkeeping (flip_to_var_before: tracker) (flip_to_var_head: tracker) (flip_to_var: tracker) (var_to_expr: env) : tracker * env = 
    let rec lookup_old_flip (flip_to_var: tracker) (x: string) : bool =
      match flip_to_var with
      | [] -> false
      | (_, new_flip, _, var, _)::tail ->
        if var = x then
          new_flip
        else
          lookup_old_flip tail x 
    in
    let rec clean_bookkeeping_s (s: string list) (var_to_expr: env) : env = 
      match s with
      | [] -> var_to_expr
      | head::tail -> clean_bookkeeping_s tail (StringMap.remove head var_to_expr)
    in
    match flip_to_var with
    | [] -> (List.rev_append flip_to_var_head []), var_to_expr
    | (used, new_flip, f, var, s)::tail -> 
      if new_flip then
        clean_bookkeeping flip_to_var_before flip_to_var_head tail (clean_bookkeeping_s s (StringMap.remove var var_to_expr))
      else
        let new_flip' = lookup_old_flip flip_to_var_before var in
        clean_bookkeeping flip_to_var_before ((used,new_flip',f,var,s)::flip_to_var_head) tail var_to_expr
  in

  let rec replace_expr_flips (flip_to_var: tracker) (e: CG.expr) (replaced_vars: string list) : CG.expr * tracker * string list = 
    match e with 
    | Flip(f) -> 
      let var, flip_to_var' = get_var [] flip_to_var f in 
      (match var with
      | None -> e, flip_to_var, replaced_vars
      | Some(v) -> Ident(v), flip_to_var', (v::replaced_vars))
    | And(e1, e2) ->
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      let e2', flip_to_var'', replaced_vars'' = replace_expr_flips flip_to_var' e2 replaced_vars' in
      And(e1', e2'), flip_to_var'', replaced_vars''
    | Or(e1, e2) ->
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      let e2', flip_to_var'', replaced_vars'' = replace_expr_flips flip_to_var' e2 replaced_vars' in
      Or(e1', e2'), flip_to_var'', replaced_vars''
    | Xor(e1, e2) ->
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      let e2', flip_to_var'', replaced_vars'' = replace_expr_flips flip_to_var' e2 replaced_vars' in
      Xor(e1', e2'), flip_to_var'', replaced_vars''
    | Eq(e1, e2)  ->
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      let e2', flip_to_var'', replaced_vars'' = replace_expr_flips flip_to_var' e2 replaced_vars' in
      Eq(e1', e2'), flip_to_var'', replaced_vars''
    | Tup(e1, e2)  ->
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      let e2', flip_to_var'', replaced_vars'' = replace_expr_flips flip_to_var' e2 replaced_vars' in
      Tup(e1', e2'), flip_to_var'', replaced_vars''
    | Snd(e1) -> 
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      Snd(e1'), flip_to_var', replaced_vars'
    | Fst(e1) -> 
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      Fst(e1'), flip_to_var', replaced_vars'
    | Not(e1) -> 
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      Not(e1'), flip_to_var', replaced_vars'
    | Observe(e1) -> 
      let e1', flip_to_var', replaced_vars' = replace_expr_flips flip_to_var e1 replaced_vars in
      Observe(e1'), flip_to_var', replaced_vars'
    | Ident(_) | _ -> e, flip_to_var, replaced_vars
  in

  let rec squeeze_expr_flips (flip_to_var: tracker) (var_to_expr: env) (e: CG.expr) (flip_vars: string list) : CG.expr * tracker * env =
    let rec update_tracker (flip_to_var_head: tracker) (flip_to_var: tracker) (var_to_expr: env) (squeezed_expr: CG.expr): CG.expr * tracker * env = 
      match flip_to_var with
      | [] -> failwith "can't find lifted flip"
      | (used, new_flip, f, v, s)::tail ->
        if List.mem v flip_vars then
          let var = fresh() in
          Ident(var), (List.rev_append flip_to_var_head ((used, new_flip, f, v, (var::s))::tail)), (StringMap.add var squeezed_expr var_to_expr)
        else
          update_tracker ((used, new_flip, f, v, s)::flip_to_var_head) tail var_to_expr squeezed_expr
    in
    match e with 
    | Flip(f) -> 
      update_tracker [] flip_to_var var_to_expr (Flip(f))
    | And(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      let e2', flip_to_var'', var_to_expr'' = squeeze_expr_flips flip_to_var' var_to_expr' e2 flip_vars in
      And(e1', e2'), flip_to_var'', var_to_expr''
    | Or(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      let e2', flip_to_var'', var_to_expr'' = squeeze_expr_flips flip_to_var' var_to_expr' e2 flip_vars in
      Or(e1', e2'), flip_to_var'', var_to_expr''
    | Xor(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      let e2', flip_to_var'', var_to_expr'' = squeeze_expr_flips flip_to_var' var_to_expr' e2 flip_vars in
      Xor(e1', e2'), flip_to_var'', var_to_expr''
    | Eq(e1, e2)  ->
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      let e2', flip_to_var'', var_to_expr'' = squeeze_expr_flips flip_to_var' var_to_expr' e2 flip_vars in
      Eq(e1', e2'), flip_to_var'', var_to_expr''
    | Tup(e1, e2)  ->
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      let e2', flip_to_var'', var_to_expr'' = squeeze_expr_flips flip_to_var' var_to_expr' e2 flip_vars in
      Tup(e1', e2'), flip_to_var'', var_to_expr''
    | Snd(e1) -> 
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      Snd(e1'), flip_to_var', var_to_expr'
    | Fst(e1) -> 
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      Fst(e1'), flip_to_var', var_to_expr'
    | Not(e1) -> 
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      Not(e1'), flip_to_var', var_to_expr'
    | Observe(e1) -> 
      let e1', flip_to_var', var_to_expr' = squeeze_expr_flips flip_to_var var_to_expr e1 flip_vars in
      Observe(e1'), flip_to_var', var_to_expr'
    | Ident(_) | _ -> e, flip_to_var, var_to_expr
  in

  let rec lift_guard_idents (flip_to_var: tracker) (var_to_expr: env) (g: CG.expr) (flips: float list): CG.expr * tracker * env = 
    match g with 
    | Ident(x) -> 
      (match StringMap.find_opt x var_to_expr with
      | None -> g, flip_to_var, var_to_expr
      | Some(expr) -> 
        (match expr with
        | Ident(x') -> 
          let in_scope = StringMap.mem x' var_to_expr in
          if in_scope then
            let flip_found, _, flip_to_var_lifted_ident = lift_ident flip_to_var x' flips [] in 
            if flip_found then
              Ident(x), flip_to_var_lifted_ident, var_to_expr
            else
              failwith "can't find lifted flips"
          else
            Ident(x), flip_to_var, var_to_expr
        | _ -> 
          let no_recurse = is_var_lifted flip_to_var x in
          if no_recurse then
            g, flip_to_var, var_to_expr
          else
            let is_squeezed = is_var_squeezed flip_to_var x in
            if is_squeezed then
              let flip_found, _, flip_to_var_lifted_ident = lift_ident flip_to_var x flips [] in 
              if flip_found then
                Ident(x), flip_to_var_lifted_ident, var_to_expr
              else
                failwith "can't find lifted flips"
            else
              let new_expr, flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr expr flips in
              let var_to_expr'' = StringMap.remove x var_to_expr' in
              g, flip_to_var', (StringMap.add x new_expr var_to_expr'')))
    | Flip(_) -> 
      let new_v = fresh() in
      let flip_found, ident_lifted, flip_to_var_lifted_ident = lift_ident flip_to_var new_v flips [] in 
      if flip_found then
        let var_to_expr' = if ident_lifted then (StringMap.add new_v g var_to_expr) else var_to_expr in
        Ident(new_v), flip_to_var_lifted_ident, var_to_expr'
      else
        failwith "can't find lifted flips"
    | Ite(g1, e1, e2) ->
      let g1', flip_to_var_new, var_to_expr_new = lift_guard_idents flip_to_var var_to_expr g1 flips in 
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var_new var_to_expr_new e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      Ite(g1', e1', e2'), flip_to_var'', var_to_expr''
    | And(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      And(e1', e2'), flip_to_var'', var_to_expr''
    | Or(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      Or(e1', e2'), flip_to_var'', var_to_expr''
    | Xor(e1, e2) ->
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      Xor(e1', e2'), flip_to_var'', var_to_expr''
    | Eq(e1, e2)  ->
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      Eq(e1', e2'), flip_to_var'', var_to_expr''
    | Tup(e1, e2)  ->
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      let e2', flip_to_var'', var_to_expr'' = lift_guard_idents flip_to_var' var_to_expr' e2 flips in
      Tup(e1', e2'), flip_to_var'', var_to_expr''
    | Snd(e1) -> 
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      Snd(e1'), flip_to_var', var_to_expr'
    | Fst(e1) -> 
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      Fst(e1'), flip_to_var', var_to_expr'
    | Not(e1) -> 
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      Not(e1'), flip_to_var', var_to_expr'
    | Observe(e1) -> 
      let e1', flip_to_var', var_to_expr' = lift_guard_idents flip_to_var var_to_expr e1 flips in
      Observe(e1'), flip_to_var', var_to_expr'
    | _ -> g, flip_to_var, var_to_expr
  in

  let rec mark_flips_as_old (flip_to_var_head: tracker) (flip_to_var: tracker) : tracker =
    match flip_to_var with
    | [] -> List.rev_append flip_to_var_head []
    | (used, _, f, v, s)::tail ->
      mark_flips_as_old ((used, false, f, v, s)::flip_to_var_head) tail
  in

  let rec down_pass_e (e: CG.expr) (flip_to_var: tracker) (var_to_expr: env) (t:tree) 
    : CG.expr * tracker * env = 
    match e with
    | Flip(f) -> 
      let var, flip_to_var' = get_var [] flip_to_var f in 
      (match var with
      | None -> e, flip_to_var, var_to_expr
      | Some(v) -> Ident(v), flip_to_var', var_to_expr)
    | Ite(g, thn, els) -> 
      (match t with
      | Node((flips, shared), thn_tree, els_tree) -> 
        (* Prepare new flip to lift *)
        let flip_to_var_fresh = mark_flips_as_old [] flip_to_var in
        let flip_to_var', var_to_expr' = lift_new_flip flip_to_var flip_to_var_fresh var_to_expr shared in

        (* Lift guard if there's a flip to be lifted within this expression *)
        let has_new_flips = (List.length shared) != 0 in 
        let has_old_flips = need_to_lift flip_to_var flips in 

        (* Lift g to the earliest matching flip that's been listed, which might be one that was just lifted or not, so just check all flips *)
        let g', flip_to_var'', var_to_expr'' =
          if (has_new_flips || has_old_flips) then
            lift_guard_idents flip_to_var' var_to_expr' g flips
          else
            g, flip_to_var', var_to_expr'
        in
        
        (* Recurse down to grab anything that needs lifting first *)
        let thn', flip_to_var_thn, var_to_expr_thn = down_pass_e thn flip_to_var'' var_to_expr'' thn_tree in
        let els', flip_to_var_els, var_to_expr_els = down_pass_e els flip_to_var'' var_to_expr'' els_tree in

        (* Concatenate squeezed stuff *)
        let var_to_expr_merged = StringMap.union (fun _ f1 _ -> Some(f1)) var_to_expr_thn var_to_expr_els in

        let flip_to_var_merged, var_to_expr_merged', els'' = concatenate_squeezed_exprs [] flip_to_var_thn flip_to_var_els var_to_expr_merged els' in
        (* Remove duplicates *)
        let flip_to_var_ready = remove_lifted [] flip_to_var_merged in

        (* Make vars of the stuff squeezed for the shared flips made here *)
        let new_expr = make_expression flip_to_var_ready var_to_expr_merged' (Ite(g', thn', els'')) in

        (* Remove the flips made here since won't need it upstream *)
        let flip_to_var_cleaned, var_to_flip_cleaned = clean_bookkeeping flip_to_var [] flip_to_var_ready var_to_expr_merged' in

        new_expr, flip_to_var_cleaned, var_to_flip_cleaned
        
      | _ -> failwith "unexpected flip tree element")
    | Let(x, e1, e2) -> 
      (match t with
      | Branch(e1_flips, e1_tree, e2_tree) ->
        if (List.length e1_flips) != 0 then
          let e1', flip_to_var', var_to_expr' = down_pass_e e1 flip_to_var var_to_expr e1_tree in
          let old_x_expr = StringMap.find_opt x var_to_expr' in
          let var_to_expr'' = StringMap.add x e1' var_to_expr' in
          let e2', flip_to_var_new, var_to_expr_new = down_pass_e e2 flip_to_var' var_to_expr'' e2_tree in
          let e1'' = 
            let potential_e = StringMap.find x var_to_expr_new in
            match potential_e with
            | Ident(x_new) ->
              if is_var_squeezed flip_to_var_new x_new then
                potential_e
              else
                e1'
            | _ -> e1'
          in
      
          let var_to_expr_restored = 
            (match old_x_expr with
            | None -> StringMap.remove x var_to_expr_new
            | Some(expr) -> StringMap.add x expr var_to_expr_new) 
          in
          Let(x, e1'', e2'), flip_to_var_new, var_to_expr_restored
        else
          let e2', flip_to_var', var_to_expr' = down_pass_e e2 flip_to_var var_to_expr e2_tree in
          Let(x, e1, e2'), flip_to_var', var_to_expr'
      | _ -> failwith "unexpected flip tree element")
    | And(_, _) | Or(_, _) | Xor(_, _) | Eq(_, _) | Tup(_, _) -> 
      let e', flip_to_var', replaced_vars = replace_expr_flips flip_to_var e [] in 
      if (List.length replaced_vars) != 0 then
        (* Squeeze the remaining flips in expr *)
        squeeze_expr_flips flip_to_var' var_to_expr e' replaced_vars
      else
        e', flip_to_var', var_to_expr
    | Snd(e1) -> 
      let e1', flip_to_var', var_to_expr' = down_pass_e e1 flip_to_var var_to_expr t in
      Snd(e1'), flip_to_var', var_to_expr'
    | Fst(e1) ->
      let e1', flip_to_var', var_to_expr' = down_pass_e e1 flip_to_var var_to_expr t in
      Fst(e1'), flip_to_var', var_to_expr'
    | Not(e1) ->
      let e1', flip_to_var', var_to_expr' = down_pass_e e1 flip_to_var var_to_expr t in
      Not(e1'), flip_to_var', var_to_expr'
    | Observe(e1) ->
      let e1', flip_to_var', var_to_expr' = down_pass_e e1 flip_to_var var_to_expr t in
      Observe(e1'), flip_to_var', var_to_expr'
    | Ident(_) | _ -> e, flip_to_var, var_to_expr
  in
  let e', _, _ = down_pass_e e [] (StringMap.empty) t in
  e'

  (* Perform code motion on flip f patterns *)
let flip_code_motion (e: CG.expr) (new_n: int) : CG.expr = 
  n := new_n;
  let _, t = up_pass e in
  let e' = down_pass e t in
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