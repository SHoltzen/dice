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

  (* codeMotionHelper: external expr -> (list of (variable name, flip param). )*)
let rec codeMotionHelper (e: ExternalGrammar.eexpr) : (string * float) list * ExternalGrammar.eexpr =
  match e with
  | Let(v, e1, e2)-> 
    let (s1, n1) = codeMotionHelper e1 in
    let (s2, n2) = codeMotionHelper e2 in
    (match e1 with
    | Flip(f1) -> ((v,f1)::(s1@s2), Let(v, n1, n2))
    | _ -> (s2, Let(v, n1, n2)))
  | Ite(g, thn, els) ->
    (* let (gc, n1) = helper g in *)
    let (tc, n2) = codeMotionHelper thn in
    let (ec, n3) = codeMotionHelper els in
    let can = (ckFlip (List.sort cmp tc) (List.sort cmp ec)) in 
    (match can with
    | [] -> ([], Ite(g, n2, n3))
    | _ -> 
      let (l, n) = codeMotionHelper (pullOut can (Ite(g, n2, n3))) in
      ([], n))

  | And(_, _) | Or(_, _) | Plus(_, _) | Eq(_, _) | Minus(_, _)
  | Neq(_, _) | Div(_, _) | Mult(_, _) | Lt(_, _) | Gt(_, _)
  | Lte(_, _) | Gte(_, _) | Tup(_, _) -> ([], e)
  | Snd(_) | Fst(_) | Not(_) | Observe(_) | Flip(_) -> ([], e)
  | _ -> ([], e)

let rec printL (f: float list) = 
  match f with
  | [] -> Format.printf "\n";
  | head::tail -> Format.printf "%f " head; (printL tail) 

let rec printVFL (fl: (String.t * float) list) = 
  match fl with
  | [] -> Format.printf "\n";
  | (var, f)::tail -> Format.printf "%f " f; (printVFL tail) 

let rec print_expr (e: ExternalGrammar.eexpr) = 
  match e with
  | Flip(f) -> (
    Format.printf "flip %f " f;
    )
  | Let(x, e1, e2) ->
    (Format.printf "let %s = " x;
    print_expr e1;
    Format.printf "in\n";
    print_expr e2)
  | Ite(g, thn, els) -> 
    (Format.printf "if ";
    print_expr g; 
    Format.printf "then\n";
    print_expr thn;
    Format.printf "\n";
    Format.printf "else ";
    Format.printf "\n";
    print_expr els)
  | True -> Format.printf "True ";
  | False -> Format.printf "False ";
  | Ident(x) -> Format.printf "%s " x;
  | _ -> Format.printf "something "

  (* Perform Code Motion on Let x = flip f patterns *)
let code_motion (p: ExternalGrammar.eexpr) : ExternalGrammar.eexpr =
  (* Format.printf "I'm in code_motion\n"; *)
  let (l, n) = codeMotionHelper p in
  (* print_expr n;
  Format.printf "\n";  *)
  n

let equal f1 f2 = if f1 = f2 then true else false

(* If there are a pair of same floats in l1 and l2 use only 1 copy *)
let rec consolidate (l1: float list) (l2: float list) : float list = 
  match l1 with
  | [] -> l2
  | head::tail ->
    let n = consolidate tail l2 in
    if (List.mem l2 head (fun x y -> x = y)) then
      n
    else
      head::n

(* Collect flips that need to be replaced *)
let rec upPass (e: ExternalGrammar.eexpr) : float list =
  match e with
  | Flip(f) -> f::[]
  | Ite(g, thn, els) ->
    (* let (gc, n1) = helper g in *)
    let n1 = upPass thn in
    let n2 = upPass els in
    let n3 = consolidate n1 n2 in 
    n3
  | Let(_, e1, e2) | And(e1, e2) | Or(e1, e2) | Plus(e1, e2) | Eq(e1, e2) | Minus(e1, e2)
  | Neq(e1, e2) | Div(e1, e2) | Mult(e1, e2) | Lt(e1, e2) | Gt(e1, e2)
  | Lte(e1, e2) | Gte(e1, e2) | Tup(e1, e2) -> 
    let n1 = upPass e1 in
    let n2 = upPass e2 in
    (n1@n2)
  | Snd(e1) | Fst(e1) | Not(e1) | Observe(e1) -> (upPass e1)
  | _ -> []
  
  (* Return the variable name of the replacement flip *)
let rec replace (f: float) (fl: (String.t * float) list) : String.t * (String.t * float) list =
  (* printVFL fl; *)
  match fl with
  | [] -> Format.printf "Flip %f\n" f; raise(Failure "Can't find corresponding flip")
  | (var, flip)::tail -> 
    (if flip = f then 
      (var, tail)
    else 
      let (v, rest) = (replace f tail) in
      (v, (var, flip)::rest))

  (* Replace the flips with corresponding variables *)
let rec downPass (e: ExternalGrammar.eexpr) (fl: (String.t * float) list) : ExternalGrammar.eexpr * (String.t * float) list =
  match e with
  | Flip(f) -> 
    (* Format.printf "Flip %f\n" f; *)
    let (v, lst) = replace f fl in
    (* printVFL lst; *)
    (Ident(v), lst)
  | Ite(g, thn, els) ->
    (* let (gc, n1) = helper g in *)
    let (te, tlst) = downPass thn fl in
    let (ee, elst) = downPass els fl in
    (Ite(g, te, ee), fl)
  | Let(v, e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Let(v, n1, n2), lst2)
  | And(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (And(n1, n2), lst2)
  | Or(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Or(n1, n2), lst2) 
  | Plus(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Plus(n1, n2), lst2) 
  | Eq(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Eq(n1, n2), lst2) 
  | Minus(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Minus(n1, n2), lst2)
  | Neq(e1, e2)  ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Neq(n1, n2), lst2)
  | Div(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Div(n1, n2), lst2)
  | Mult(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Mult(n1, n2), lst2)
  | Lt(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Lt(n1, n2), lst2)
  | Gt(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Gt(n1, n2), lst2)
  | Lte(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Lte(n1, n2), lst2) 
  | Gte(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Gte(n1, n2), lst2)
  | Tup(e1, e2) ->
    let (n1, lst1) = downPass e1 fl in
    let (n2, lst2) = downPass e2 lst1 in
    (Tup(n1, n2), lst2)    
  | Snd(e1) ->
    let (n1, lst1) = downPass e1 fl in
    (Snd(n1), lst1)
  | Fst(e1) ->
    let (n1, lst1) = downPass e1 fl in
    (Fst(n1), lst1)
  | Not(e1) ->
    let (n1, lst1) = downPass e1 fl in
    (Not(n1), lst1)
  | Observe(e1) ->
    let (n1, lst1) = downPass e1 fl in
    (Observe(n1), lst1)
  | _ -> (e, fl)

  (* Return variable assignments to flips and list of (var, flip val) *)
let rec addFlips (fl: float list) (i: int) : ExternalGrammar.eexpr * (String.t * float) list = 
  match fl with 
  | [] -> (True, [])
  | head::tail -> 
    let var = Printf.sprintf "%d" i in
    let (e, vf) = addFlips tail (i+1) in
    (Let(var, Flip(head), e), (var, head)::vf)
  
  (* Glue variable assignments of flips to parsed program *)
let rec glue_together (vars: ExternalGrammar.eexpr) (e: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  match vars with
  | True -> e
  | Let(v,e1,e2) -> Let(v, e1, (glue_together e2 e))
  | _ -> e

  (* Perform code motion on flip f patterns *)
let flip_code_motion (p: ExternalGrammar.eexpr) : ExternalGrammar.eexpr = 
  (* Format.printf "I'm in flip_code_motion\n"; *)
  let fl = upPass p in
  (* printL fl; *)
  let (vars, vl) = addFlips fl 0 in
  (* print_expr vars;
  Format.printf "\n"; *)
  (* printVFL vl; *)
  let (inner, l) = downPass p vl in
  let e = glue_together vars inner in
  (* print_expr e;
  Format.printf "\n"; *)
  e

let optimize (p:ExternalGrammar.program) : ExternalGrammar.program = 
  let n = flip_code_motion p.body in
  { functions= p.functions; body= n }