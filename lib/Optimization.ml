open Stdlib
open ExternalGrammar

(* assumptions:
    - guards cannot be optimized
    - code motions from different levels
*)

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
  | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2)
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) | Gt(e1, e2)
  | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> [], Leaf
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> [], Leaf
  | _ -> [], Leaf

  (* Replace the flips with corresponding variables *)
let rec downPass (e: ExternalGrammar.eexpr) 
  (fl: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
  (i: int) (t: tree)
    : ExternalGrammar.eexpr * int * (String.t * float) list * (String.t * float * (String.t * ExternalGrammar.eexpr) list) list =
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

  and get_fl (i: int) (vf: float list) (gl: (String.t * ExternalGrammar.eexpr) list)
              (c: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list)
                : (String.t * float * (String.t * ExternalGrammar.eexpr) list) list =
    match vf with
    | [] -> c
    | head::tail -> 
      let var = Printf.sprintf "_%d" i in
      get_fl (i+1) tail gl ((var, head, gl)::c)

  and update_fl (fl: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
    (gl: (String.t * ExternalGrammar.eexpr)) (lower_flips: float list)
    (c: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list)
    : (String.t * float * (String.t * ExternalGrammar.eexpr) list) list =
    match fl with
    | [] -> List.rev c
    | (v,f,gl1)::tail ->
      if List.mem f lower_flips then
        update_fl tail gl (remove_one lower_flips (fun flip -> f = flip)) ((v,f,(gl::gl1))::c)
      else
        update_fl tail gl lower_flips fl

  and merge_fl (fl1: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
    (fl2: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
    (c: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
    : (String.t * float * (String.t * ExternalGrammar.eexpr) list) list =
    let rec search_fl2 (v1,f1,gl1) fl2 =
      let rec merge_gl gl1 gl2 =
        match gl1 with
        | [] -> gl2
        | (v1, e1)::tail ->
          List.filter (fun (v2, e2) -> not (v1 = v2)) gl2
          |> merge_gl tail 
      in

      match fl2 with
      | [] -> None
      | (v2,f2,gl2)::tail2 ->
        if v1 = v2 then
          Some(v1, f1, (merge_gl gl1 gl2)@gl1)
        else
          search_fl2 (v1,f1,gl1) tail2
    in

    match fl1 with
    | [] -> List.rev c
    | head1::tail1 ->
        (match search_fl2 head1 fl2 with
        | None -> merge_fl tail1 fl2 (head1::c)
        | Some(r) -> merge_fl tail1 fl2 (r::c))
  
  and collapse_fl (fl: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list) 
    (vl: String.t list)
    (vf: (String.t * ExternalGrammar.eexpr) list)
    (to_add: (String.t * ExternalGrammar.eexpr) list) 
    (pass_up: (String.t * float * (String.t * ExternalGrammar.eexpr) list) list)
    : (String.t * ExternalGrammar.eexpr) list * (String.t * float * (String.t * ExternalGrammar.eexpr) list) list =
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
    | (v,f,gl)::tail -> 
      if List.mem v vl then
        collapse_fl tail vl ((v,Flip(f))::vf) (merge_gl gl to_add) pass_up
      else
        collapse_fl tail vl vf to_add ((v,f,gl)::pass_up)
    
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
  and add_lets (el: (String.t * ExternalGrammar.eexpr) list) (inner: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
    match el with 
    | [] -> inner
    | (v, expr)::tail -> 
      add_lets tail (Let(v, expr, inner))

  and has_flip (e: ExternalGrammar.eexpr) : bool =
    match e with
    | Flip(f) -> true
    | Ite(g, thn, els) -> (has_flip g) || (has_flip thn) || (has_flip els)
    | Let(_, e1, e2)
    | And(e1, e2)
    | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2) 
    | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) 
    | Gt(e1, e2) | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> (has_flip e1) || (has_flip e2)
    | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> (has_flip e1)
    | _ -> false
  in 

  match e with
  | Flip(f) -> 
    let vf = List.map (fun (v, f, gl) -> (v,f)) fl in
    if f = 0.0 then
      False, i, vf, fl
    else if f = 1.0 then
      True, i, vf, fl
    else
      (match replace f vf with
      | None -> Flip(f), i, vf, fl
      | Some (v, lst) -> Ident(v), i, lst, fl)

  | Ite(g, thn, els) ->
    (* Find common flips between subtrees *)
    (match t with
      | Node((llist, rlist), left, right) -> 
        let node_list = find_match llist rlist in
        let upper_flips = List.map (fun (v, f, gl) -> f) fl in
        let new_flips = find_no_match node_list upper_flips in
        let lower_flips = find_match (List.rev_append llist rlist) upper_flips in
        let pull_g = has_flip g in

        (* add guard to appropriate fl *)
        let gv = (Printf.sprintf "_%d" i) in
        let fl2 = if not pull_g || lower_flips = [] then fl else update_fl fl (gv, g) lower_flips [] in
        let i2 = if not pull_g || lower_flips = [] then i else i+1 in
        
        if new_flips = [] then
          if lower_flips = [] then
            Ite(g, thn, els), i2, [], fl2
          else
            (* Pass flips down *)
            let (thn_expr, thn_i, thn_vf, thn_fl) = downPass thn fl2 i2 left in
            let (els_expr, els_i, els_vf, els_fl) = downPass els fl2 thn_i right in
            let new_g = if pull_g then Ident(gv) else g in
            Ite(new_g, thn_expr, els_expr), els_i, [], (merge_fl thn_fl els_fl [])
        else
          let ggl = if pull_g then [(gv,g)] else [] in
          let i3 = if pull_g then i2 + 1 else i2 in
          let new_fl = get_fl i3 new_flips ggl [] in
          let new_v = List.map (fun (v,f,gl) -> v) new_fl in
          let pass_down_fl = new_fl@fl2 in
          let i4 = i3 + (List.length new_fl) in

          (* Pass flips down *)
          let (thn_expr, thn_i, thn_vf, thn_fl) = downPass thn pass_down_fl i4 left in
          let (els_expr, els_i, els_vf, els_fl) = downPass els pass_down_fl thn_i right in

          (* add flips in lexical order *)
          let fl3 = merge_fl thn_fl els_fl [] in
          (* printFL fl3; *)
          let to_add, pass_up_fl = collapse_fl fl3 new_v [] [] [] in
          (* printEL to_add; *)

          let new_g = if pull_g then Ident(gv) else g in
          let new_expr = add_lets to_add (Ite(new_g, thn_expr, els_expr)) in
          new_expr, els_i, [], pass_up_fl

      | _ -> e, i, List.map (fun (v, f, gl) -> (v,f)) fl, fl)
  | Let(v, e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, i1, vf1, fl1) = downPass e1 fl i t1 in
      let (n2, i2, vf2, fl2) = downPass e2 fl1 i1 t2 in
      (Let(v, n1, n2), i2, vf2, fl2)
    | _ -> e, i, List.map (fun (v, f, gl) -> (v,f)) fl, fl)
  | And(e1, e2)
  | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2) 
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) 
  | Gt(e1, e2) | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> e, i, List.map (fun (v, f, gl) -> (v,f)) fl, fl
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> e, i, List.map (fun (v, f, gl) -> (v,f)) fl, fl
  | _ -> e, i, List.map (fun (v, f, gl) -> (v,f)) fl, fl

  (* Perform code motion on flip f patterns *)
let flip_code_motion (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  let fl, t = upPass e in
  let (e1, i1, vf1, fl1) = downPass e [] 0 t in
  e1

(* let rec merge_branch (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
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
  | _ -> e *)

let optimize (p:ExternalGrammar.program) : ExternalGrammar.program = 
  let n1 = flip_code_motion p.body in
  (* let n2 = merge_branch n1 in  *)
  { functions= p.functions; body= n1 }