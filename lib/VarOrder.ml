(** Defines an intermediate AST that tags each new variable production source
    with an index. This AST is used by the compiler to generate variables in a
    particular order. *)

open Core
open Cudd
open VarState

module CG = CoreGrammar

type strategy =
    Default
  | DFS

(** A tagged expression where, each time a new logical variable is introduced,
    it is tagged with its order *)
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
  | Flip of float * int (** the int is order of the flip *)
  | Let of String.t * texpr * texpr * (int btree) (** the int btree is the order of the argument *)
  | FuncCall of String.t * texpr List.t * (int, int) Map.Poly.t 
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
  | FuncCall(id, _, _) ->
    (try Map.Poly.find_exn env id
    with _ -> failwith (Format.sprintf "Could not find function '%s' during typechecking" id))


(** Core function grammar *)
type func = {
  name: String.t;
  args: CG.arg List.t;
  body: texpr;

  local_bools: int List.t;
  arg_bools: int List.t;
}
[@@deriving sexp_of]

type fenv = (String.t, func) Map.Poly.t
[@@deriving sexp_of]


let type_of_fun env f : CG.typ =
  (* set up the type environment and then type the body *)
  let new_env = List.fold ~init:env f.args ~f:(fun acc (name, typ) ->
      Map.Poly.add_exn acc ~key:name ~data:typ
    ) in
  type_of new_env f.body

type program = {
  functions: fenv;
  body: texpr;
}
[@@deriving sexp_of]

let string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)


(** create a new variable tree
   `c` is a counter that tracks that tracks which variable is currently the last
   in the order *)
let rec mk_tree (c: int ref) (t:CG.typ) : int VarState.btree =
  match t with
  | TBool ->
    let v = !c in
    c := !c + 1;
    Leaf(v)
  | TTuple(l, r) ->
    let l = mk_tree c l in
    let r = mk_tree c r in
    Node(l, r)

(** Updates the order of a tagged AST `e` according to `map` *)
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
  | FuncCall(name, targs, order_map) ->
    FuncCall(
      name,
      List.map targs (update_order map),
      Map.Poly.map order_map (Hashtbl.Poly.find_exn map)
      (* arg_range *)
    )


(** creates a tagged AST from a core grammar AST. The goal here is simply to associate each
    created logical variable with a unique identifier.

    By default, this should be the same as the depth-first order used by the compiler.

    TOOD: Make sure that this is the case. I suspect right now that these orders
    are different, and that using the default ordering from this module will
    cause a serious performance regression.
*)
let rec from_cg_h (count: int ref) (t: CG.tenv) (f:fenv) (e: CG.expr) : texpr =
  match e with
  | And(l, r) ->
    let l = from_cg_h count t f l in
    let r = from_cg_h count t f r in
    And(l, r)
  | Or(l, r) ->
    let l = from_cg_h count t f l in
    let r = from_cg_h count t f r in
    Or(l, r)
  | Eq(l, r) ->
    let l = from_cg_h count t f l in
    let r = from_cg_h count t f r in
    Eq(l, r)
  | Xor(l, r) ->
    let l = from_cg_h count t f l in
    let r = from_cg_h count t f r in
    Xor(l, r)
  | Tup(l, r) ->
    let l = from_cg_h count t f l in
    let r = from_cg_h count t f r in
    Tup(l, r)
  | Not(e) -> Not(from_cg_h count t f e)
  | Ident(s) -> Ident(s)
  | Sample(e) -> Sample(from_cg_h count t f e)
  | Fst(e) -> Fst(from_cg_h count t f e)
  | Snd(e) -> Snd(from_cg_h count t f e)
  | True -> True
  | False -> False
  | Flip(x) ->
    let i = !count in
    count := !count + 1;
    Flip(x, i)
  | Ite(g, thn, els) ->
    let g = from_cg_h count t f g in
    let thn = from_cg_h count t f thn in
    let els = from_cg_h count t f els in
    Ite(g, thn, els)
  | Let(x, e1, e2) ->
    let te1 = CG.type_of t e1 in
    let rece1 = from_cg_h count t f e1 in
    let tree = mk_tree count te1 in
    let t' = Map.Poly.set t ~key:x ~data:te1 in
    let rece2 = from_cg_h count t' f e2 in
    Let(x, rece1, rece2, tree)
  | Observe(e) -> Observe(from_cg_h count t f e)
  | FuncCall(name, args) ->
    let targs = List.map args (from_cg_h count t f) in
    let func = Map.Poly.find_exn f name in
    let bool_count = (List.length func.arg_bools) + (List.length func.local_bools) in
    let init_count = !count in
    let order_map_args = List.fold ~init:Map.Poly.empty ~f:(fun map i ->
      let map' = Map.Poly.set map ~key:i ~data:!count in
      count := !count +1;
      map'
    ) func.arg_bools in
    (* let arg_range = (init_count, !count) in *)
    let order_map = List.fold ~init:order_map_args ~f:(fun map i ->
      let map' = Map.Poly.set map ~key:i ~data:!count in
      count := !count +1;
      map'
    ) func.local_bools in
    FuncCall(name, targs, order_map)


let from_cg_func count (tenv: CG.tenv) (fenv: fenv) (f: CG.func) : func =
  (* add the arguments to the type environment *)
  let init_count = !count in
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      let _tree = mk_tree count typ in
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let count_with_args = !count in
  let conv = from_cg_h count tenvwithargs fenv f.body in
  (* convert arguments *)
  {name = f.name;
   args = f.args;
   body = conv;

   arg_bools = List.range init_count count_with_args;
   local_bools = List.range count_with_args !count;
   }

(** a map from each variable to its parents. This encodes a dependency graph. *)
type cdfg = (int, int Set.Poly.t) Hashtbl.Poly.t
(** a map from each identifier to the variables that it depends on *)
type env = (String.t, (int Set.Poly.t) btree) Map.Poly.t

let build_cdfg (p: program) (f: fenv) =
  (** construct a CDFG for an expression. Returns a `btree` of sets of integers
      for handling tuples. *)
  let rec cdfg_e (cdfg: cdfg) (env: env) e =
    match e with
    | And(e1, e2)
    | Or(e1, e2)
    | Eq(e1, e2)
    | Xor(e1, e2) ->
      (* for binary expressions, simply take the union of whichever dependencies are
         present in the two children *)
      let s1 = extract_leaf (cdfg_e cdfg env e1) in
      let s2 = extract_leaf (cdfg_e cdfg env e2) in
      Leaf(Set.union s1 s2)
    | Not(e1)
    | Observe(e1) -> cdfg_e cdfg env e1
    | Sample(e) -> cdfg_e cdfg env e
    | True
    | False -> Leaf(Set.Poly.empty)
    | Ident(x) ->
      (* this is why we have the environment map *)
      Map.Poly.find_exn env x
    | Fst(e) ->
      extract_l (cdfg_e cdfg env e)
    | Snd(e) -> extract_r (cdfg_e cdfg env e)
    | Tup(e1, e2) ->
      let s1 = cdfg_e cdfg env e1 in
      let s2 = cdfg_e cdfg env e2 in
      Node(s1, s2)
    | Flip(_, v) ->
      (* for flips, depend only on the flip's Boolean indicator *)
      Hashtbl.Poly.add_exn cdfg ~key:v ~data:Set.Poly.empty;
      Leaf(Set.Poly.of_list [v])
    | Ite(g, thn, els) ->
      let gdeps = extract_leaf (cdfg_e cdfg env g) in
      let thndeps = cdfg_e cdfg env thn in
      let elsdeps = cdfg_e cdfg env els in
      (* take the union all the dependencies of the guard, then branch, and else-branch *)
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
    | FuncCall(name, args, order_map) ->
      let argdeps = List.map args (cdfg_e cdfg env) in
      (* let (arg_start, arg_end) = arg_range in *)
      let func = Map.Poly.find_exn f name in
      let argtrees = 
        if (List.length func.arg_bools) > 0 then
          let count = ref (List.nth_exn func.arg_bools 0) in 
          List.map func.args ~f:(fun (_, typ) ->
            map_tree (mk_tree count typ) (fun i -> Set.Poly.of_list [Map.Poly.find_exn order_map i])
          )
        else
          []
        in
      List.iter (List.zip_exn argtrees argdeps) ~f:(fun (tree, dep) ->
        let _a = map_tree (zip_tree tree dep) (fun (curx, curdep) ->
          Hashtbl.Poly.add_exn cdfg ~key:(Set.Poly.choose_exn curx) ~data:curdep;
        ) in ()
      );
      let argenv = List.fold ~init:Map.Poly.empty ~f:(fun argenv ((name, _), tree) ->
        Map.Poly.set argenv ~key:name ~data:tree
      ) (List.zip_exn func.args argtrees) in
      let order_map_h = Hashtbl.Poly.create () in
      List.iter (Map.Poly.to_alist order_map) ~f:(fun (k,v) -> Hashtbl.Poly.add_exn order_map_h ~key:k ~data:v);
      let refreshed_body = update_order order_map_h func.body in
      cdfg_e cdfg argenv refreshed_body
    in
  let tbl : cdfg = Hashtbl.Poly.create () in
  let r = cdfg_e tbl Map.Poly.empty p.body in
  (r, tbl)

(** This is a variable ordering function that takes a CDFG as an argument
    and produces a possible variable ordering. Produces a map from variable
    identifiers to their new positions in the order.

    It perform a depth-first topological sort.
    TODO: Test this and make sure that it is correct
 *)
let dfs_ts ?start (cdfg: cdfg) =
  let map = Hashtbl.Poly.create () in
  let init_count = match start with Some x -> x | None -> 0 in
  let count = ref init_count in
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

let from_cg_prog strategy (p: CG.program) =
  let count = ref 0 in
  (* TODO right now, functions are not handled by variable reordering. We would
     add this feature here. *)
  let (tenv, fenv) = List.fold p.functions ~init:(Map.Poly.empty, Map.Poly.empty) ~f:(fun (tenv, fenv) i ->
      let tenvwithargs = List.fold i.args ~init:tenv ~f:(fun acc (name, typ) ->
          Map.Poly.set acc ~key:name ~data:typ
        ) in
      let t = CG.type_of tenvwithargs i.body in
      let conv = from_cg_func count tenv fenv i in
      (* print_endline i.name; *)
  (* [%sexp_of: texpr] conv.body |> Sexp.to_string_hum |> print_endline;     *)
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      let fenv' = Map.Poly.set fenv ~key:i.name ~data:conv in
      (tenv', fenv')
    ) in
  let dummy_count = !count in
  let convbody = from_cg_h count tenv fenv p.body in
  (* print_endline "* MAIN *"; [%sexp_of: texpr] convbody |> Sexp.to_string_hum |> print_endline; *)
  match strategy with
  | Default ->
    (!count, {functions=fenv; body=convbody})
  | DFS ->
    let prog = {functions = fenv; body = convbody} in
    let (_, cdfg) = build_cdfg prog fenv in
    (* print_endline "\nBEFORE"; [%sexp_of: texpr] prog.body |> Sexp.to_string_hum |> print_endline; *)
    (* [%sexp_of: (int, int Set.Poly.t) Hashtbl.Poly.t] cdfg |> Sexp.to_string_hum |> print_endline; *)
    let order = dfs_ts ~start:dummy_count cdfg in
    
    let updated = update_order order prog.body in
    (* print_endline "\nAFTER"; [%sexp_of: texpr]  updated |> Sexp.to_string_hum |> print_endline; *)
    (!count, {functions=fenv; body=updated})
