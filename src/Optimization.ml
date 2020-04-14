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

let equal f1 f2 = if f1 = f2 then true else false

(* Remove one item from list l if predicate function f returns true *)
let rec remove_one l f = 
  match l with
  | [] -> []
  | head::tail -> if f head then tail else head::(remove_one tail f)

(* If there are a pair of same items in l1 and l2 use only 1 copy *)
let rec consolidate (l1: 'a list) (l2: 'a list) : 'a list = 
  match l1 with
  | [] -> l2
  | head::tail ->
    let new_l2 = remove_one l2 (fun x -> x = head) in
    head::(consolidate tail new_l2)

type tree = 
  | Node of (float list * float list) * tree * tree
  | Branch of tree * tree
  | Leaf 

(* Collect flips that need to be replaced *)
let rec upPass (e: ExternalGrammar.eexpr) : float list * tree =
  match e with
  | Flip(f) -> [f], Leaf
  | Ite(g, thn, els) ->
    let n1, t1 = upPass thn in
    let n2, t2 = upPass els in
    let t3 = Node((n1, n2), t1, t2) in
    let n3 = consolidate n1 n2 in 
    (n3, t3)
  | Let(_, e1, e2) | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2)
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) | Gt(e1, e2)
  | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> 
    let n1, t1 = upPass e1 in
    let n2, t2 = upPass e2 in
    (n1@n2, Branch(t1, t2))
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> (upPass e1)
  | _ -> [], Leaf
  
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

(* Return each matching pair from two list *)
let rec find_match (l1: float list) (l2: float list) : float list = 
  match l1 with
  | [] -> []
  | head::tail ->
    if List.exists l2 (fun x -> x = head) then
      let new_l2 = remove_one l2 (fun x -> x = head) in
      head::(find_match tail new_l2)
    else
      (find_match tail l2)

(* Return each non-pair from two list *)
let rec find_no_match (l1: float list) (l2: float list) : float list =
  match l1 with
  | [] -> []
  | head::tail -> 
    if List.exists l2 (fun x -> x = head) then
      let new_l2 = remove_one l2 (fun x -> x = head) in
      (find_no_match tail new_l2)
    else
      head::(find_no_match tail l2)

let rec flip_to_vf (i: int) (fl: float list) : (String.t * float) list =
  match fl with
  | [] -> []
  | head::tail -> 
    let var = Printf.sprintf "%d" i in
    (var, head)::(flip_to_vf (i+1) tail)

(* Return variable assignments to flips *)
let rec add_flips (fl: (String.t * float) list) (inner: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  match fl with 
  | [] -> inner
  | (v, f)::tail -> 
    let e = add_flips tail inner in
    Let(v, Flip(f), e)

  (* Replace the flips with corresponding variables *)
let rec downPass (e: ExternalGrammar.eexpr) (fl: (String.t * float) list) (i: int) (t: tree): ExternalGrammar.eexpr * (String.t * float) list =
  match e with
  | Flip(f) -> 
    (match replace f fl with
    | None -> Flip(f), fl
    | Some (v, lst) -> Ident(v), lst)

  | Ite(g, thn, els) ->
    (* Find common flips between subtrees *)
    (match t with
    | Node((llist, rlist), left, right) -> 
      let node_list = find_match llist rlist in
      let upper_flips = List.map fl (fun (v, f) -> f) in
      let new_flips = find_no_match node_list upper_flips in
      let new_vf = flip_to_vf i new_flips in
      let pass_down_vf = fl@new_vf in

      let new_i = i + (List.length new_flips) in
      (* Pass flips down *)
      let (thn_expr, thn_lst) = downPass thn pass_down_vf new_i left in
      let (els_expr, els_lst) = downPass els pass_down_vf new_i right in

      (add_flips new_vf (Ite(g, thn_expr, els_expr))), fl
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
  | Or(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Or(n1, n2), lst2)
    | _ -> e, fl)
  | Plus(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Plus(n1, n2), lst2)
    | _ -> e, fl)
  | Eq(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Eq(n1, n2), lst2)
    | _ -> e, fl)
  | Minus(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Minus(n1, n2), lst2)
    | _ -> e, fl)
  | Neq(e1, e2)  ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Neq(n1, n2), lst2)
    | _ -> e, fl)
  | Div(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Div(n1, n2), lst2)
    | _ -> e, fl)
  | Mult(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Mult(n1, n2), lst2)
    | _ -> e, fl)
  | Lt(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Lt(n1, n2), lst2)
    | _ -> e, fl)
  | Gt(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Gt(n1, n2), lst2)
    | _ -> e, fl)
  | Lte(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Lte(n1, n2), lst2)
    | _ -> e, fl)
  | Gte(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Gte(n1, n2), lst2)
    | _ -> e, fl)
  | Tup(e1, e2) ->
    (match t with
    | Branch(t1, t2) -> 
      let (n1, lst1) = downPass e1 fl i t1 in
      let (n2, lst2) = downPass e2 lst1 i t2 in
      (Tup(n1, n2), lst2)
    | _ -> e, fl)   
  | Snd(e1) ->
    let (n1, lst1) = downPass e1 fl i t in
    (Snd(n1), lst1)
  | Fst(e1) ->
    let (n1, lst1) = downPass e1 fl i t in
    (Fst(n1), lst1)
  | Not(e1) ->
    let (n1, lst1) = downPass e1 fl i t in
    (Not(n1), lst1)
  | Observe(e1) ->
    let (n1, lst1) = downPass e1 fl i t in
    (Observe(n1), lst1)
  | _ -> (e, fl)
  
  (* Glue variable assignments of flips to parsed program *)
let rec glue_together (vars: ExternalGrammar.eexpr) (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  match vars with
  | True -> e
  | Let(v,e1,e2) -> Let(v, e1, (glue_together e2 e))
  | _ -> e

  (* Perform code motion on flip f patterns *)
let flip_code_motion (p: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  let fl, t = upPass p in
  let (e, l) = downPass p [] 0 t in
  e

let optimize (p:ExternalGrammar.program) : ExternalGrammar.program = 
  let n = flip_code_motion p.body in
  { functions= p.functions; body= n }