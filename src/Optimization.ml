open Core
open ExternalGrammar

(* Return true if item is in lst *)
let rec check item lst : bool = 
  match lst with
  | [] -> false
  | head::tail -> if (head = item) then true else (check item tail)

  (* Return list of (variable, flip float) that appear in both lists *)
let rec ckFlip l1 l2 : 'a list = 
  match l1 with
  | [] -> []
  | head::tail -> 
    (if (check head l2) then 
      (* let (v, f) = head in ( *)
      (* (Format.printf "let %s = flip %f\n" v f;  *)
      (match l2 with
      | [] -> []
      | hd::tl -> head::(ckFlip tail tl))
    else (ckFlip tail l2))

  (* Remove let x = flip f from e *)
let rec poHelp item e : ExternalGrammar.eexpr = 
  match e with
  | Ite(g, thn, els) ->
    let t = poHelp item thn in 
    let el = poHelp item els in
    Ite(g, t, el)
  | Let(v, e1, e2) ->
    let (vi, fi) = item in
    (if vi = v && e1 = Flip(fi) then
      e2
    else
      Let(v, e1, (poHelp item e2)))
  | _ -> e
    
  (* Pull let x = flip f out from if then else *)
let rec pullOut l1 expr : ExternalGrammar.eexpr = 
  match l1 with
  | [] -> expr
  | head::[] -> let (v,f) = head in Let(v, Flip(f), (poHelp head expr))
  | head::tail -> let (v,f) = head in Let(v, Flip(f), (poHelp head (pullOut tail expr)))

  (* Comparison function for sort. Sort by flip, breaking ties with variable name *)
let cmp t1 t2 : int = 
  let (v1, f1) = t1 in
  let (v2, f2) = t2 in
  if f1 < f2 then -1 else if f1 > f2 then 1 else if v1 < v2 then -1 else if v1 > v2 then 1 else 0

  (* helper: external expr -> (list of (variable name, flip param). )*)
let rec helper (e: ExternalGrammar.eexpr) : (string * float) list * ExternalGrammar.eexpr =
  match e with
  | Let(v, e1, e2)-> 
    let (s1, n1) = helper e1 in
    let (s2, n2) = helper e2 in
    (match e1 with
    | Flip(f1) -> ((v,f1)::(s1@s2), Let(v, n1, n2))
    | _ -> (s2, Let(v, n1, n2)))
  | Ite(g, thn, els) ->
    (* let (gc, n1) = helper g in *)
    let (tc, n2) = helper thn in
    let (ec, n3) = helper els in
    let can = (ckFlip (List.sort cmp tc) (List.sort cmp ec)) in 
    (match can with
    | [] -> ([], Ite(g, n2, n3))
    | _ -> 
      let (l, n) = helper (pullOut can (Ite(g, n2, n3))) in
      ([], n))

  | And(_, _) | Or(_, _) | Plus(_, _) | Eq(_, _) | Minus(_, _)
  | Neq(_, _) | Div(_, _) | Mult(_, _) | Lt(_, _) | Gt(_, _)
  | Lte(_, _) | Gte(_, _) | Tup(_, _) -> ([], e)
  | Snd(_) | Fst(_) | Not(_) | Observe(_) | Flip(_) -> ([], e)
  | _ -> ([], e)

let rec print_expr (e: ExternalGrammar.eexpr) = 
  match e with
  | Flip(f) -> (
    Format.printf "flip %f " f;
    e
    )
  | Let(x, e1, e2) ->
    (Format.printf "let %s = " x;
    let _ = (print_expr e1) in 
    Format.printf "in \n";
    let _ = (print_expr e2) in e)
  | Ite(g, thn, els) -> 
    (Format.printf "if ";
    let _ = (print_expr g) in 
    Format.printf "then ";
    let _ = (print_expr thn) in 
    Format.printf "else ";
    let _ = (print_expr els) in e)
  | True -> Format.printf "True "; e
  | False -> Format.printf "False "; e
  | Ident(x) -> Format.printf "%s " x; e
  | _ -> Format.printf "something "; e

let code_motion (p: ExternalGrammar.program) : ExternalGrammar.program =
  Format.printf "I'm in code_motion\n";
  let (l, n) = helper p.body in
  let x = (print_expr n) in
  Format.printf "\n"; 
  { functions= p.functions; body= x }