(** Defines an intermediate AST that tags each new variable production source
    with an index. This AST is used by the compiler to generate variables in a
    particular order. *)

open Core
open Cudd
open VarState

module CG = CoreGrammar

type texpr =
  | And of texpr * texpr
  | Or of texpr * texpr
  | Eq of texpr * texpr
  | Xor of texpr * texpr
  | Not of texpr
  | Ident of String.t
  | Sample of texpr
  | Fst of texpr
  | Snd of texpr
  | Tup of texpr * texpr
  | Ite of texpr * texpr * texpr
  | True
  | False
  | Flip of float * int
  | Let of String.t * texpr * texpr * (int btree)
  | FuncCall of String.t * texpr List.t
  | Observe of texpr
[@@deriving sexp_of]
and fcall = {
  fname: String.t;
  args: texpr
}

let string_of_texpr e =
  Sexp.to_string_hum (sexp_of_texpr e)

let rec type_of env e : CG.typ =
  match e with
  | And(_, _) | Xor(_, _) | Eq(_, _) | Or(_, _) | Not(_) | True | False | Flip(_) | Observe(_) -> TBool
  | Ident(s) -> (try Map.Poly.find_exn env s
    with _ -> failwith (Format.sprintf "Could not find variable %s during typechecking" s))
  | Sample(e) -> type_of env e
  | Fst(e1) ->
    (match type_of env e1 with
     | TTuple(l, _) -> l
     | _ -> failwith "Type error: expected tuple")
  | Snd(e1) ->
    (match type_of env e1 with
     | TTuple(_, r) -> r
     | _ -> failwith "Type error: expected tuple")
  | Tup(e1, e2) ->
    let t1 = type_of env e1 in
    let t2 = type_of env e2 in
    TTuple(t1 ,t2)
  | Let(x, e1, e2, _) ->
    let te1 = type_of env e1 in
    type_of (Map.Poly.set env ~key:x ~data:te1) e2
  | Ite(_, thn, _) ->
    let t1 = type_of env thn in
    (* let t2 = type_of env els in *)
    (* assert (t1 == t2); *)
    t1
  | FuncCall(id, _) ->
    (try Map.Poly.find_exn env id
    with _ -> failwith (Format.sprintf "Could not find function '%s' during typechecking" id))


(** Core function grammar *)
type func = {
  name: String.t;
  args: CG.arg List.t;
  body: texpr;
}
[@@deriving sexp_of]

let type_of_fun env f : CG.typ =
  (* set up the type environment and then type the body *)
  let new_env = List.fold ~init:env f.args ~f:(fun acc (name, typ) ->
      Map.Poly.add_exn acc ~key:name ~data:typ
    ) in
  type_of new_env f.body

type program = {
  functions: func List.t;
  body: texpr;
}
[@@deriving sexp_of]

let string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)


let rec mk_tree (c: int ref) (t:CG.typ) : int VarState.btree =
  match t with
  | TBool ->
    let v = !c in
    c := !c + 1;
    Leaf(v)
  | TTuple(l, r) -> Node(mk_tree c l, mk_tree c r)

let rec from_cg_h (count: int ref) (t: CG.tenv) (e: CG.expr) : texpr =
  match e with
  | And(l, r) -> And(from_cg_h count t l, from_cg_h count t r)
  | Or(l, r) -> Or(from_cg_h count t l, from_cg_h count t r)
  | Eq(l, r) -> Eq(from_cg_h count t l, from_cg_h count t r)
  | Xor(l, r) -> Xor(from_cg_h count t l, from_cg_h count t r)
  | Tup(l, r) -> Tup(from_cg_h count t l, from_cg_h count t r)
  | Not(e) -> Not(from_cg_h count t e)
  | Ident(s) -> Ident(s)
  | Sample(e) -> Sample(from_cg_h count t e)
  | Fst(e) -> Fst(from_cg_h count t e)
  | Snd(e) -> Snd(from_cg_h count t e)
  | True -> True
  | False -> False
  | Flip(f) ->
    let i = !count in
    count := !count + 1;
    Flip(f, i)
  | Ite(g, thn, els) ->
    Ite(from_cg_h count t g,
        from_cg_h count t thn,
        from_cg_h count t els)
  | Let(x, e1, e2) ->
    let te1 = CG.type_of t e1 in
    let rece1 = from_cg_h count t e1 in
    let t' = Map.Poly.set t ~key:x ~data:te1 in
    let tree = mk_tree count te1 in
    let rece2 = from_cg_h count t' e2 in
    Let(x, rece1, rece2, tree)
  | Observe(e) -> Observe(from_cg_h count t e)
  | FuncCall(_) -> failwith "Function translation not implemented"

let from_cg_func count (tenv: CG.tenv) (f: CG.func) : func =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let conv = from_cg_h count tenvwithargs f.body in
  (* convert arguments *)
  {name = f.name;
   args = f.args;
   body = conv}

(** a map from each variable to its parents *)
type cdfg = (int, int Set.Poly.t) Hashtbl.Poly.t
type env = (String.t, (int Set.Poly.t) btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let build_cdfg (p: program) =
  let rec cdfg_e (cdfg: cdfg) (env: env) e =
    match e with
    | And(e1, e2)
    | Or(e1, e2)
    | Eq(e1, e2)
    | Xor(e1, e2) ->
      let s1 = extract_leaf (cdfg_e cdfg env e1) in
      let s2 = extract_leaf (cdfg_e cdfg env e2) in
      Leaf(Set.union s1 s2)
    | Not(e1)
    | Observe(e1) -> cdfg_e cdfg env e1
    | Sample(e) -> cdfg_e cdfg env e
    | True
    | False -> Leaf(Set.Poly.empty)
    | Ident(x) ->
      Map.Poly.find_exn env x
    | Fst(e) -> extract_l (cdfg_e cdfg env e)
    | Snd(e) -> extract_r (cdfg_e cdfg env e)
    | Tup(e1, e2) ->
      let s1 = cdfg_e cdfg env e1 in
      let s2 = cdfg_e cdfg env e2 in
      Node(s1, s2)
    | Flip(_, v) ->
      Hashtbl.Poly.add_exn cdfg ~key:v ~data:Set.Poly.empty;
      Leaf(Set.Poly.of_list [v])
    | Ite(g, thn, els) ->
      let gdeps = extract_leaf (cdfg_e cdfg env g) in
      let thndeps = cdfg_e cdfg env thn in
      let elsdeps = cdfg_e cdfg env els in
      (* union all deps *)
      map_tree (zip_tree thndeps elsdeps) (fun (l, r) ->
          Set.Poly.union_list [l; r; gdeps]
        )
    | Let(x, e1, e2, v) ->
      let e1deps = cdfg_e cdfg env e1 in
      let settree = map_tree v (fun i -> Set.Poly.of_list [i]) in
      let env' = Map.Poly.set env ~key:x ~data:settree in
      let e2deps = cdfg_e cdfg env' e2 in

      (* update the dependencies for all the variables in x *)
      let _a = map_tree (zip_tree v e1deps) (fun (curx, curdep) ->
          Hashtbl.Poly.add_exn cdfg ~key:curx ~data:curdep;
        ) in
      e2deps
    | _ -> failwith "not implemented" in
  (* ignore functions for now *)
  let tbl : cdfg = Hashtbl.Poly.create () in
  let r = cdfg_e tbl Map.Poly.empty p.body in
  (r, tbl)

(** depth-first topological sort **)
let dfs_ts (cdfg: cdfg) =
  let map = Hashtbl.Poly.create () in
  let count = ref 0 in
  let rec visit (n: int) =
    if Hashtbl.Poly.mem map n then () else
      (let parlist : int List.t = Set.Poly.to_list (Hashtbl.Poly.find_exn cdfg n) in
       List.iter parlist ~f:(fun i ->
           (* Format.printf "Parent of %d: %d\n" n i; *)
           visit i
         );
       Hashtbl.Poly.set map ~key:n ~data:!count;
       (* Format.printf "Mapped %d -> %d\n" n !count; *)
       count := !count + 1;
      ) in
  let l = Hashtbl.Poly.keys cdfg |> List.sort ~compare:Int.compare |> List.rev in
  List.iter l ~f:(fun n ->
      visit n
    );
  map

let rec update_order map e =
  match e with
  | And(e1, e2) -> And(update_order map e1, update_order map e2)
  | Or(e1, e2) -> Or(update_order map e1, update_order map e2)
  | Xor(e1, e2) -> Xor(update_order map e1, update_order map e2)
  | Eq(e1, e2) -> Eq(update_order map e1, update_order map e2)
  | Not(e1) -> Not(update_order map e1)
  | Observe(e1) -> Observe(update_order map e1)
  | Sample(e1) -> Sample(update_order map e1)
  | True -> True
  | False -> False
  | Ident(x) -> Ident(x)
  | Fst(e) -> Fst(update_order map e)
  | Snd(e) -> Snd(update_order map e)
  | Tup(e1, e2) ->
    Tup(update_order map e1, update_order map e2)
  | Flip(f, v) -> Flip(f, Hashtbl.Poly.find_exn map v)
  | Ite(g, thn, els) -> Ite(update_order map g,
                            update_order map thn,
                            update_order map els)
  | Let(x, e1, e2, v) ->
    Let(x, update_order map e1, update_order map e2, map_tree v (Hashtbl.Poly.find_exn map))
  | _ -> failwith "not implemented"


let from_cg_prog (p: CG.program) =
  let count = ref 0 in
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let tenvwithargs = List.fold i.args ~init:tenv ~f:(fun acc (name, typ) ->
          Map.Poly.set acc ~key:name ~data:typ
        ) in
      let t = CG.type_of tenvwithargs i.body in
      let conv = from_cg_func count tenv i in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let convbody = from_cg_h count tenv p.body in
  let prog = {functions = functions; body = convbody} in
  let (_, cdfg) = build_cdfg prog in (** todo here: use the returned BDD?*)
  let order = dfs_ts cdfg in
  let updated = update_order order prog.body in
  (* Format.printf "Before: %s\n\n" (string_of_texpr prog.body);
   * Format.printf "After: %s\n\n" (string_of_texpr updated); *)
  (!count, {functions=functions; body=updated})
