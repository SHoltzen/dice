open Core
open ExternalGrammar

let rec check item lst = 
  match lst with
  | [] -> false
  | head::tail -> if (head = item) then true else (check item tail)

let rec ckFlip l1 l2 = 
  match l1 with
  | [] -> []
  | head::tail -> 
    (if (check head l2) then 
      (* let (v, f) = head in ( *)
      (* (Format.printf "let %s = flip %f\n" v f;  *)
      (let hd::tl = l2 in
      head::(ckFlip tail tl))
    else (ckFlip tail l2))

let rec poHelp item e = 
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
    
let rec pullOut l1 expr = 
  match l1 with
  | [] -> expr
  | head::[] -> let (v,f) = head in Let(v, Flip(f), (poHelp head expr))
  | head::tail -> let (v,f) = head in Let(v, Flip(f), (poHelp head (pullOut tail expr)))

let cmp t1 t2 = 
  let (v1, f1) = t1 in
  let (v2, f2) = t2 in
  if f1 < f2 then -1 else if f1 > f2 then 1 else if v1 < v2 then -1 else if v1 > v2 then 1 else 0

let rec helper (e: ExternalGrammar.eexpr) =
  match e with
  | And(e1, e2)
  | Or(e1, e2)
  | Plus(e1, e2)
  | Eq(e1, e2)
  | Minus(e1, e2)
  | Neq(e1, e2)
  | Div(e1, e2)
  | Mult(e1, e2)
  | Lt(e1, e2)
  | Gt(e1, e2)
  | Lte(e1, e2)
  | Gte(e1, e2)
  | Tup(e1, e2) -> ([], e)
  | Snd(e1) | Fst(e1)
  | Not(e1)
  | Observe(e1) -> ([], e)

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

  | Flip(f) -> ([], e)
  | _ -> ([], e)

let rec print_expr (e: ExternalGrammar.eexpr) = 
  match e with
  | Flip(f) -> (
    Format.printf "flip %f " f;
    e
    )
  | Let(x, e1, e2) ->
    (Format.printf "let %s = " x;
    let tmp = (print_expr e1) in 
    Format.printf "in \n";
    let tmp = (print_expr e2) in e)
  | Ite(g, thn, els) -> 
    (Format.printf "if ";
    let tmp = (print_expr g) in 
    Format.printf "then ";
    let tmp = (print_expr thn) in 
    Format.printf "else ";
    let tmp = (print_expr els) in e)
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