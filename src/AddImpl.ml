open Core
open Cudd

type expr =
    Or of expr * expr
  | And of expr * expr
  | Not of expr
  | Ident of string

let rec string_of_expr e =
  match e with
  | Or(e1, e2) -> sprintf "(|| %s %s)" (string_of_expr e1) (string_of_expr e2)
  | And(e1, e2) -> sprintf "(&& %s %s)" (string_of_expr e1) (string_of_expr e2)
  | Not(e) -> sprintf "(! %s)" (string_of_expr e)
  | Ident(s) -> s

type stmt =
    Assgn of string * expr
  | Flip of string * float
  | If of expr * stmt * stmt
  | Observe of expr
  | Seq of stmt List.t

let rec string_of_stmt s =
  match s with
  | Assgn(s, e) -> sprintf "%s=%s\n" s (string_of_expr e)
  | Flip(s, f) -> sprintf "%s=flip(%f)\n" s f
  | If(e, s1, s2) -> sprintf "if(%s)\n{%s}\nelse\n{%s}" (string_of_expr e) (string_of_stmt s1) (string_of_stmt s2)
  | Observe(e) -> sprintf "observe(%s)\n" (string_of_expr e)
  | Seq([]) -> ""
  | Seq(x::xs) -> sprintf "%s%s" (string_of_stmt x) (string_of_stmt (Seq(xs)))

type prog = stmt list

type env = (string, Cudd.Bdd.dt) Hashtbl.Poly.t

let rec compile_expr mgr env e =
  match e with
  | Ident(s) ->
    (match Hashtbl.Poly.find env s with
     | Some(v) -> v
     | None -> failwith (sprintf "Could not find %s" s))
  | And(e1, e2) ->
    let sub1 = compile_expr mgr env e1 in
    let sub2 = compile_expr mgr env e2 in
    Cudd.Bdd.dand sub1 sub2
  | Or(e1, e2) ->
    let sub1 = compile_expr mgr env e1 in
    let sub2 = compile_expr mgr env e2 in
    Cudd.Bdd.dor sub1 sub2
  | Not(e) ->
    let sub1 = compile_expr mgr env e in
    Cudd.Bdd.dnot sub1

let rec compile_stmt mgr env stmt =

  let r = match stmt with
  | Assgn(s, e) ->
    let newv = Cudd.Bdd.newvar mgr in
    Hashtbl.Poly.add_exn env s newv;
    let sube = compile_expr mgr env e in
    Cudd.Add.of_bdd (Bdd.eq sube newv)
  | Flip(s, f) ->
    (* let newv =  in *)
    let newv = Hashtbl.Poly.find_or_add env s ~default:(fun () -> Cudd.Bdd.newvar mgr) in
    (* Hashtbl.Poly.add_exn env s newv; *)
    Cudd.Add.ite newv (Cudd.Add.cst mgr f) (Cudd.Add.cst mgr (1.0 -. f))
  | Observe(e) ->
    let e = compile_expr mgr env e in
    Cudd.Add.of_bdd e
  | If(guard, s1, s2) ->
    let sub1 = compile_stmt mgr env s1 in
    let sub2 = compile_stmt mgr env s2 in
    Cudd.Add.ite (compile_expr mgr env guard) sub1 sub2
  | Seq([]) -> Cudd.Add.cst mgr 1.0
  | Seq(x::xs) ->
    let sub1 = compile_stmt mgr env x in
    Cudd.Add.mul sub1 (compile_stmt mgr env (Seq(xs))) in
  Format.printf "compiled %s to size: %d\n" (string_of_stmt stmt) (Add.size r);
  r

let prob stmt expr =
  let mgr = Cudd.Man.make_d ?numSlots:(Some 30000) () in
  let tbl = Hashtbl.Poly.create () in
  let cs = compile_stmt mgr tbl stmt in
  let e = compile_expr mgr tbl expr in
  let varcube = Hashtbl.Poly.fold tbl ~init:(Bdd.dtrue mgr) ~f:(fun ~key ~data acc ->
      Bdd.dand acc data
    ) in
  (* compute Z*)
  Format.printf "size: %d\n" (Add.size cs);
  Format.printf "paths: %f\n" (Add.nbpaths cs);
  let z = Add.dval (Add.exist varcube cs) in
  let constrained = Cudd.Add.mul (Cudd.Add.of_bdd e) cs in
  let p = Add.dval (Add.exist varcube constrained) in
  p /. z
