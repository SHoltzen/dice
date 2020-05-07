open Core
open ExternalGrammar

let rec printL (f: float list) = 
  match f with
  | [] -> Format.printf "\n";
  | head::tail -> Format.printf "%f " head; (printL tail) 

let rec printVFL (fl: (String.t * float) list) = 
  match fl with
  | [] -> Format.printf "\n";
  | (var, f)::tail -> Format.printf "%f " f; (printVFL tail) 

(* Remove one item from list l if predicate function f returns true *)
let rec remove_one l f = 
  match l with
  | [] -> []
  | head::tail -> if f head then tail else head::(remove_one tail f)

type tree = 
  | Node of (float list * float list) * tree * tree
  | Branch of tree * tree
  | Leaf 

(* Collect flips that need to be replaced *)
let rec upPass (e: ExternalGrammar.eexpr) : float list * tree =
  (* If there are a pair of same items in l1 and l2 use only 1 copy *)
  let rec consolidate (l1: 'a list) (l2: 'a list) : 'a list = 
    match l1 with
    | [] -> l2
    | head::tail ->
      let new_l2 = remove_one l2 (fun x -> x = head) in
      head::(consolidate tail new_l2)
  in

  match e with
  | Flip(f) -> 
    if f = 0.0 || f = 1.0 then
      [], Leaf
    else 
      [f], Leaf
  | Ite(g, thn, els) ->
    let n0, t0 = upPass g in
    let n1, t1 = upPass thn in
    let n2, t2 = upPass els in
    let t3 = Node((n1, n2), t1, t2) in
    let n3 = consolidate n1 n2 in 
    (* (n3, t3) *)
    (n0@n3, Branch(t0, t3))
  | Let(_, e1, e2) -> 
    let n1, t1 = upPass e1 in
    let n2, t2 = upPass e2 in
    (n1@n2, Branch(t1, t2))
  | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2)
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) | Gt(e1, e2)
  | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> [], Leaf
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> [], Leaf
  | _ -> [], Leaf

  (* Replace the flips with corresponding variables *)
let rec downPass (e: ExternalGrammar.eexpr) (fl: (String.t * float) list) (i: int) (t: tree): ExternalGrammar.eexpr * (String.t * float) list =
  (* Return the variable name of the replacement flip *)
  let rec replace (f: float) (fl: (String.t * float) list) : (String.t * (String.t * float) list) option =
    match fl with
    | [] -> None
    | (var, flip)::tail -> 
      if flip = f then
        Some (var, tail)
      else 
        match replace f tail with
        | None -> None
        | Some (v, rest) -> Some (v, (var, flip)::rest)

  and flip_to_vf (i: int) (fl: float list) : (String.t * float) list =
    match fl with
    | [] -> []
    | head::tail -> 
      let var = Printf.sprintf "_%d" i in
      (var, head)::(flip_to_vf (i+1) tail)

  (* Return each matching pair from two list *)
  and find_match (l1: float list) (l2: float list) : float list = 
    match l1 with
    | [] -> []
    | head::tail ->
      if List.exists l2 (fun x -> x = head) then
        let new_l2 = remove_one l2 (fun x -> x = head) in
        head::(find_match tail new_l2)
      else
        (find_match tail l2)

  (* Return each non-pair from two list *)
  and find_no_match (l1: float list) (l2: float list) : float list =
    match l1 with
    | [] -> []
    | head::tail -> 
      if List.exists l2 (fun x -> x = head) then
        let new_l2 = remove_one l2 (fun x -> x = head) in
        (find_no_match tail new_l2)
      else
        head::(find_no_match tail l2)

  (* Return variable assignments to flips *)
  and add_flips (fl: (String.t * float) list) (inner: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
    match fl with 
    | [] -> inner
    | (v, f)::tail -> 
      let e = add_flips tail inner in
      Let(v, Flip(f), e)

  and pull_guard_flips (g: ExternalGrammar.eexpr) (fl: float list) : float list = 
    match g with
    | Flip(f) -> f::fl
    | Ite(g1, thn, els) ->
      pull_guard_flips g1 fl
      |> pull_guard_flips thn
      |> pull_guard_flips els
    | Let(_, e1, e2) | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2)
    | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) | Gt(e1, e2)
    | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> 
      pull_guard_flips e1 fl
      |> pull_guard_flips e2 
    | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> pull_guard_flips e1 fl
    | _ -> fl
  in

  match e with
  | Flip(f) -> 
    if f = 0.0 then
      False, fl
    else if f = 1.0 then
      True, fl
    else
      (match replace f fl with
      | None -> Flip(f), fl
      | Some (v, lst) -> Ident(v), lst)

  | Ite(g, thn, els) ->
    (* Find common flips between subtrees *)
    (match t with
    | Branch(t1, t2) -> 
      let (g_expr, _) = downPass g fl i t1 in
      (* any leftover flips also need to be pulled out *)
      let guard_flips = pull_guard_flips g_expr [] in
      let guard_vf = flip_to_vf i guard_flips in
      let guard_i = i + (List.length guard_flips) in
      let new_g, _ = downPass g_expr guard_vf i t1 in

      (match t2 with
      | Node((llist, rlist), left, right) -> 
        let node_list = find_match llist rlist in
        let upper_flips = List.map fl (fun (v, f) -> f) in
        let new_flips = find_no_match node_list upper_flips in
        let new_vf = (flip_to_vf guard_i new_flips) in
        let pass_down_vf = fl@new_vf in

        let new_i = guard_i + (List.length new_flips) in
        (* Pass flips down *)
        let (thn_expr, thn_lst) = downPass thn pass_down_vf new_i left in
        let (els_expr, els_lst) = downPass els pass_down_vf new_i right in

        (add_flips guard_vf (add_flips new_vf (Ite(new_g, thn_expr, els_expr)))), fl
      | _ -> e, fl)
    | _ -> e, fl)
  | Let(v, e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Let(v, n1, n2), lst2)
    | _ -> e, fl)
  | And(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (And(n1, n2), lst2)
    | _ -> e, fl)
  | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2) 
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) 
  | Gt(e1, e2) | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> (e, fl)
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> (e, fl)
  | _ -> (e, fl)

  (* Perform code motion on flip f patterns *)
let flip_code_motion (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  let fl, t = upPass e in
  let (e1, l) = downPass e [] 0 t in
  e1

let rec merge_branch (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  match e with
  | Ite(g, thn, els) ->
    let n1 = merge_branch thn in
    let n2 = merge_branch els in
    (match n1,n2 with
    | True, False | False, True -> g
    | _, _ ->
      if n1 = n2 then
        n1
      else 
        Ite(g, n1, n2))
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
  | Plus(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Plus(n1, n2)
  | Eq(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Eq(n1, n2)
  | Minus(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Minus(n1, n2)
  | Neq(e1, e2)  ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Neq(n1, n2)
  | Div(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Div(n1, n2)
  | Mult(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Mult(n1, n2)
  | Lt(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Lt(n1, n2)
  | Gt(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Gt(n1, n2)
  | Lte(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Lte(n1, n2)
  | Gte(e1, e2) ->
    let n1 = merge_branch e1 in
    let n2 = merge_branch e2 in
    Gte(n1, n2)
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

let optimize (p:ExternalGrammar.program) : ExternalGrammar.program = 
  let n1 = flip_code_motion p.body in
  let n2 = merge_branch n1 in 
  { functions= p.functions; body= n2 }