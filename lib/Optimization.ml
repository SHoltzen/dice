open Stdlib
module CG = CoreGrammar
open CG
(* assumptions:
    - guards cannot be optimized
    - no optimizing on functions

*)

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let rec printL (f: float list) = 
  match f with
  | [] -> Format.printf "\n";
  | head::tail -> Format.printf "%f " head; (printL tail) 

let rec printVFL (fl: (String.t * float) list) = 
  match fl with
  | [] -> Format.printf "\n";
  | (_, f)::tail -> Format.printf "%f " f; (printVFL tail) 

let rec printFL (fl: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) =
  let rec printGL gl =
    match gl with
    | [] -> Format.printf "]\n";
    | (v, e)::tail ->
      Format.printf "(%s, %s)," v (ExternalGrammar.string_of_eexpr e); (printGL tail)
  in
  match fl with
  | [] -> Format.printf "\n";
  | (v, f, gl)::tail ->
    Format.printf "%s, %f, [" v f;
    printGL gl;
    printFL tail

let rec printEL (el: (String.t * ExternalGrammar.eexpr) list) = 
  match el with
  | [] -> Format.printf "\n";
  | (v, e)::tail ->
    Format.printf "%s, %s\n" v (ExternalGrammar.string_of_eexpr e); (printEL tail)

(* Optimization pass *)
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
let rec upPass (e: CG.expr) : float list * tree =
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
  | Ite(_, thn, els) ->
    (* let n0, t0 = upPass g in *)
    let n1, t1 = upPass thn in
    let n2, t2 = upPass els in
    let t3 = Node((n1, n2), t1, t2) in
    let n3 = consolidate n1 n2 in 
    (n3, t3)
    (* (n3, Branch(t0, t3)) *)
  | Let(_, e1, e2) -> 
    let n1, t1 = upPass e1 in
    let n2, t2 = upPass e2 in
    (n1@n2, Branch(t1, t2))
  | _ -> [], Leaf

  (* Replace the flips with corresponding variables *)
let rec downPass (e: CG.expr) 
  (fl: (String.t * float * (String.t * CG.expr) list * bool) list) 
  (t: tree)
    : CG.expr * (String.t * float * (String.t * CG.expr) list * bool) list =
  (* Return the variable name of the replacement flip *)
  (* TODO: bug where used flips aren't removed! *)
  let rec replace (f: float) (fl:  (String.t * float * (String.t * CG.expr) list * bool) list) 
    : (String.t * ((String.t * float * (String.t * CG.expr) list * bool) list)) option =
    match fl with
    | [] -> None
    | (var, flip, gl, used)::tail -> 
      if flip = f && not used then
        Some (var, (var, flip, gl, true)::tail)
      else 
        match replace f tail with
        | None -> None
        | Some (v, rest) -> Some (v, (var, flip, gl, used)::rest)

  and get_fl (vf: float list) (gl: (String.t * CG.expr) list)
              (c: (String.t * float * (String.t * CG.expr) list * bool) list)
                : (String.t * float * (String.t * CG.expr) list * bool) list =
    match vf with
    | [] -> c
    | head::tail -> 
      let var = fresh() in
      get_fl tail gl ((var, head, gl, false)::c)

  and update_fl (fl: (String.t * float * (String.t * CG.expr) list * bool) list) 
    (gl: (String.t * CG.expr)) (lower_flips: float list)
    (c: (String.t * float * (String.t * CG.expr) list * bool) list)
    : (String.t * float * (String.t * CG.expr) list * bool) list =
    match fl with
    | [] -> List.rev c
    | (v,f,gl1,used)::tail ->
      if List.mem f lower_flips then
        update_fl tail gl (remove_one lower_flips (fun flip -> f = flip)) ((v,f,(gl::gl1),used)::c)
      else
        update_fl tail gl lower_flips fl

  and merge_fl (fl1: (String.t * float * (String.t * CG.expr) list * bool) list) 
    (fl2: (String.t * float * (String.t * CG.expr) list * bool) list) 
    (c: (String.t * float * (String.t * CG.expr) list * bool) list) 
    : (String.t * float * (String.t * CG.expr) list * bool) list =
    let rec search_fl2 (v1,f1,gl1,used1) fl2 =
      let rec merge_gl gl1 gl2 =
        match gl1 with
        | [] -> gl2
        | (v1, _)::tail ->
          List.filter (fun (v2, _) -> not (v1 = v2)) gl2
          |> merge_gl tail 
      in

      match fl2 with
      | [] -> None
      | (v2,_,gl2,_)::tail2 ->
        if v1 = v2 then
          Some(v1, f1, (merge_gl gl1 gl2)@gl1, used1)
        else
          search_fl2 (v1,f1,gl1,used1) tail2
    in

    match fl1 with
    | [] -> List.rev c
    | head1::tail1 ->
        (match search_fl2 head1 fl2 with
        | None -> merge_fl tail1 fl2 (head1::c)
        | Some(r) -> merge_fl tail1 fl2 (r::c))
  
  and collapse_fl (fl: (String.t * float * (String.t * CG.expr) list * bool) list) 
    (vl: String.t list)
    (vf: (String.t * CG.expr) list)
    (to_add: (String.t * CG.expr) list) 
    (pass_up: (String.t * float * (String.t * CG.expr) list * bool) list)
    : (String.t * CG.expr) list * (String.t * float * (String.t * CG.expr) list * bool) list =
    let rec merge_gl gl c =
      match gl with
      | [] -> c
      | head::tail ->
        if List.mem head c then
          merge_gl tail c
        else
          merge_gl tail (head::c)
    in

    match fl with
    | [] -> (List.rev_append vf (List.rev to_add)), List.rev pass_up
    | (v,f,gl,used)::tail -> 
      if List.mem v vl then
        collapse_fl tail vl ((v,Flip(f))::vf) (merge_gl gl to_add) pass_up
      else
        collapse_fl tail vl vf to_add ((v,f,gl,used)::pass_up)
    
  (* Return each matching pair from two list *)
  and find_match (l1: float list) (l2: float list) : float list = 
    match l1 with
    | [] -> []
    | head::tail ->
      if List.mem head l2 then
        let new_l2 = remove_one l2 (fun x -> x = head) in
        head::(find_match tail new_l2)
      else
        (find_match tail l2)

  (* Return each non-pair from two list *)
  and find_no_match (l1: float list) (l2: float list) : float list =
    match l1 with
    | [] -> []
    | head::tail -> 
      if List.mem head l2 then
        let new_l2 = remove_one l2 (fun x -> x = head) in
        (find_no_match tail new_l2)
      else
        head::(find_no_match tail l2)

  (* Return variable assignments to expr *)
  and add_lets (el: (String.t * CG.expr) list) (inner: CG.expr) : CG.expr = 
    match el with 
    | [] -> inner
    | (v, expr)::tail -> 
      add_lets tail (Let(v, expr, inner))

  and has_flip (e: CG.expr) : bool =
    match e with
    | Flip(_) -> true
    | Ite(g, thn, els) -> (has_flip g) || (has_flip thn) || (has_flip els)
    | Let(_, e1, e2)
    | And(e1, e2)
    | Or(e1, e2) | Eq(e1, e2) | Xor(e1, e2) 
    | Tup(e1, e2) -> (has_flip e1) || (has_flip e2)
    | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> (has_flip e1)
    | _ -> false
  in 

  match e with
  | Flip(f) ->
    (match replace f fl with
    | None -> Flip(f), fl
    | Some (v, new_fl) -> Ident(v), new_fl)

  | Ite(g, thn, els) ->
    (* Find common flips between subtrees *)
    (match t with
      | Node((llist, rlist), left, right) -> 
        let node_list = find_match llist rlist in
        let upper_flips = List.map (fun (_, f, _, _) -> f) fl in
        let new_flips = find_no_match node_list upper_flips in
        let lower_flips = find_match (List.rev_append llist rlist) upper_flips in
        let pull_g = has_flip g in

        (* add guard to appropriate fl *)
        let gv = fresh() in
        let fl2 = if not pull_g || lower_flips = [] then fl else update_fl fl (gv, g) lower_flips [] in
        
        if new_flips = [] then
          if lower_flips = [] then
            Ite(g, thn, els), fl2
          else
            (* Pass flips down *)
            let (thn_expr, thn_fl) = downPass thn fl2 left in
            let (els_expr, els_fl) = downPass els fl2 right in
            let new_g = if pull_g then Ident(gv) else g in
            Ite(new_g, thn_expr, els_expr), (merge_fl thn_fl els_fl [])
        else
          let ggl = if pull_g then [(gv,g)] else [] in
          let new_fl = get_fl new_flips ggl [] in
          let new_v = List.map (fun (v,_,_,_) -> v) new_fl in
          let pass_down_fl = new_fl@fl2 in

          (* Pass flips down *)
          let (thn_expr, thn_fl) = downPass thn pass_down_fl left in
          let (els_expr, els_fl) = downPass els pass_down_fl right in

          (* add flips in lexical order *)
          let fl3 = merge_fl thn_fl els_fl [] in
          (* printFL fl3; *)
          let to_add, pass_up_fl = collapse_fl fl3 new_v [] [] [] in
          (* printEL to_add; *)

          let new_g = if pull_g then Ident(gv) else g in
          let new_expr = add_lets to_add (Ite(new_g, thn_expr, els_expr)) in
          new_expr, pass_up_fl

      | _ -> e, fl)
  | Let(v, e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, fl1) = downPass e1 fl t1 in
      let (n2, fl2) = downPass e2 fl1 t2 in
      (Let(v, n1, n2), fl2)
    | _ -> e, fl)
  | _ -> e, fl

  (* Perform code motion on flip f patterns *)
let flip_code_motion (e: CG.expr) (new_n: int) : CG.expr = 
  n := new_n;
  let _, t = upPass e in
  let (e1, _) = downPass e [] t in
  e1

let rec merge_branch (e: CG.expr) : CG.expr = 
  match e with
  | Flip(f) ->
    if f = 0.0 then
      False
    else if f = 1.0 then
      True
    else
      Flip(f)
  | Ite(g, thn, els) ->
    let n1 = merge_branch thn in
    let n2 = merge_branch els in
    (* Ite(g, n1, n2) *)
    (match n1,n2 with
    | True, False -> g
    | False, True -> Not(g)
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

let do_optimize (e: CG.expr) (new_n: int) : CG.expr = 
  let e1 = flip_code_motion e new_n in
  let e2 = merge_branch e1 in
  e2
