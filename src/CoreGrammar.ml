open Core
open Cudd
open Wmc
open BddUtil

type expr =
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Ident of String.t
  | Fst of expr
  | Snd of expr
  | Tup of expr * expr
  | Ite of expr * expr * expr
  | Discrete of float List.t
  | Eq of expr * expr
  | Plus of expr * expr
  | Int of int * int  (* sz, v *)
  | True
  | False
  | Flip of float
  | Let of String.t * expr * expr
  | FuncCall of fcall
  | Observe of expr
[@@deriving sexp]
and fcall = {
  assgn: String.t List.t;
  fname: String.t;
  args: expr
}
[@@deriving sexp]


let rec string_of_expr e =
  match e with
  | And(e1, e2) -> sprintf "%s && %s" (string_of_expr e1) (string_of_expr e2)
  | Or(e1, e2) -> sprintf "%s || %s" (string_of_expr e1) (string_of_expr e2)
  | Eq(e1, e2) -> sprintf "%s == %s" (string_of_expr e1) (string_of_expr e2)
  | Plus(e1, e2) -> sprintf "%s + %s" (string_of_expr e1) (string_of_expr e2)
  | Not(e) -> sprintf "! %s" (string_of_expr e)
  | Ite(g, thn, els) ->
    sprintf "if %s then %s else %s"
      (string_of_expr g) (string_of_expr thn) (string_of_expr els)
  | Let(id, e1, e2) ->
    sprintf "let %s = %s in %s"
      id (string_of_expr e1) (string_of_expr e2)
  | Observe(e) -> sprintf "observe %s" (string_of_expr e)
  | True -> "true"
  | False -> "false"
  | Flip(f) -> sprintf "flip %f" f
  | Ident(s) -> s
  | Snd(e) -> sprintf "snd %s" (string_of_expr e)
  | Fst(e) -> sprintf "fst %s" (string_of_expr e)
  | Tup(e1, e2) -> sprintf "(%s, %s)" (string_of_expr e1) (string_of_expr e2)
  | Discrete(l) ->
    sprintf "Discrete(%s)" (List.to_string ~f:string_of_float l)
  | Int(sz, value) -> sprintf "Int(%d, %d)" sz value

type typ =
    Bool
  | Discrete of int (* argument is the size of the discrete domain *)
  | Tup of typ * typ
[@@deriving sexp]

(** Core function grammar *)
type func = {
  name: String.t;
  args: String.t List.t;
  body: expr;
}
[@@deriving sexp]

type compiled_func = {
  args: Bdd.dt List.t;
  flips: Bdd.dt List.t;
}

type program = {
  functions: func List.t;
  body: expr;
}
[@@deriving sexp]

let rec from_external_expr (e: ExternalGrammar.eexpr) : expr =
  match e with
  | And(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in And(s1, s2)
  | Or(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Or(s1, s2)
  | Plus(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Plus(s1, s2)
  | Eq(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Eq(s1, s2)
  | Not(e) -> Not(from_external_expr e)
  | Flip(f) -> Flip(f)
  | Ident(s) -> Ident(s)
  | Discrete(l) -> Discrete(l)
  | Int(sz, v) -> Int(sz, v)
  | True -> True
  | False -> False
  | Observe(e) -> Observe(from_external_expr e)
  | Let(x, e1, e2) -> Let(x, from_external_expr e1, from_external_expr e2)
  | Ite(g, thn, els) -> Ite(from_external_expr g, from_external_expr thn, from_external_expr els)
  | Snd(e) -> Snd(from_external_expr e)
  | Fst(e) -> Fst(from_external_expr e)
  | Tup(e1, e2) -> Tup(from_external_expr e1, from_external_expr e2)


(** The result of compiling an expression. A pair (value, normalizing constant) *)
type varstate =
    BddLeaf of Bdd.dt
  | IntLeaf of Bdd.dt List.t

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

(** Holds a compiled var state and the normalizing BDD *)
type state = (varstate btree * Bdd.dt)

let extract_bdd (state: varstate btree) =
  match state with
  | Leaf(BddLeaf(bdd)) -> bdd
  | _ -> failwith "invalid bdd extraction"

let extract_discrete(state: varstate btree) =
  match state with
  | Leaf(IntLeaf(l)) -> l
  | _ -> failwith "invalid bdd extraction"


let rec map_tree (s:'a btree) (f: 'a -> 'b) : 'b btree =
  match s with
  | Leaf(bdd) -> Leaf(f bdd)
  | Node(l, r) -> Node(map_tree l f, map_tree r f)

let rec zip_tree (s1: 'a btree) (s2: 'b btree) =
  match (s1, s2) with
  | (Leaf(a), Leaf(b)) -> Leaf((a, b))
  | (Node(a_l, a_r), Node(b_l, b_r)) ->
    Node(zip_tree a_l b_l, zip_tree a_r b_r)
  | _ -> failwith "could not zip trees, incompatible shape"

type compile_context = {
  man: Man.dt;
  name_map: (int, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
}

type env = (String.t, varstate btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let new_context () =
  let man = Man.make_d () in
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man=man;
   name_map=names;
   weights= weights}

let rec compile_expr (ctx: compile_context) (env: env) e : state =
  match e with
  | And(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let v = Leaf(BddLeaf(Bdd.dand (extract_bdd v1) (extract_bdd v2))) in
    let z = Bdd.dand z1 z2 in
    (v, z)
  | Or(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let v = Leaf(BddLeaf(Bdd.dor (extract_bdd v1) (extract_bdd v2))) in
    let z =Bdd.dand z1 z2 in
    (v, z)
  | Not(e) ->
    let (v1, z1) = compile_expr ctx env e in
    let v = Bdd.dnot (extract_bdd v1) in
    (Leaf(BddLeaf(v)), z1)
  | True -> (Leaf(BddLeaf(Bdd.dtrue ctx.man)), Bdd.dtrue ctx.man)
  | False -> (Leaf(BddLeaf(Bdd.dfalse ctx.man)), Bdd.dtrue ctx.man)
  | Ident(s) ->
    (match Map.Poly.find env s with
     | Some(r) -> (r, Bdd.dtrue ctx.man)
     | _ -> failwith (sprintf "Could not find Boolean variable %s" s))
  | Tup(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    (Node(v1, v2), Bdd.dand z1 z2)
  | Ite(g, thn, els) ->
    let (vg, zg) = compile_expr ctx env g in
    let (vthn, zthn) = compile_expr ctx env thn in
    let (vels, zels) = compile_expr ctx env els in
    let gbdd = extract_bdd vg in
    let zipped = zip_tree vthn vels in
    let v' = map_tree zipped (fun (thn_state, els_state) ->
        match (thn_state, els_state) with
        | (BddLeaf(thn_bdd), BddLeaf(els_bdd)) ->
          BddLeaf(Bdd.dor (Bdd.dand gbdd thn_bdd) (Bdd.dand (Bdd.dnot gbdd) els_bdd))
        | (IntLeaf(l1), IntLeaf(l2)) ->
          let zipped_l = try List.zip_exn l1 l2
            with _ -> failwith (Format.sprintf "Type error: length mismatch between %s and %s"
                                  (string_of_expr thn) (string_of_expr els)) in
          let l = List.map zipped_l ~f:(fun (thn_bdd, els_bdd) ->
              Bdd.dor (Bdd.dand gbdd thn_bdd) (Bdd.dand (Bdd.dnot gbdd) els_bdd)
            ) in
          IntLeaf(l)
        | _ -> failwith (sprintf "Type error")
      ) in
    let z' = Bdd.dand zg (Bdd.dor (Bdd.dand zthn gbdd)
                            (Bdd.dand zels (Bdd.dnot gbdd))) in
    (v', z')
  | Fst(e) ->
    let (v, z) = compile_expr ctx env e in
    let v' = (match v with
     | Node(l, _) -> l
     | _ -> failwith "calling `fst` on non-tuple") in
    (v', z)
  | Snd(e) ->
    let (v, z) = compile_expr ctx env e in
    let v' = (match v with
     | Node(_, r) -> r
     | _ -> failwith "calling `snd` on non-tuple") in
    (v', z)
  | Flip(f) ->
    let new_f = Bdd.newvar ctx.man in
    let var_lbl = Bdd.topvar new_f in
    Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.f, f);
    Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "f%f" f);
    (Leaf(BddLeaf(new_f)), Bdd.dtrue ctx.man)
  | Observe(g) ->
    let (g, z) = compile_expr ctx env g in
    (Leaf(BddLeaf(Bdd.dtrue ctx.man)), Bdd.dand (extract_bdd g) z)
  | Let(x, e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let env' = Map.Poly.set env ~key:x ~data:v1 in
    let (v2, z2) = compile_expr ctx env' e2 in
    (v2, Bdd.dand z1 z2)
  | Discrete(l) ->
    (* first construct a list of all the properly parameterized flips *)
    let (bdd_l, _) = List.fold ~init:([], 1.0) l ~f:(fun (cur_l, cur_z) param ->
        let new_param = param /. cur_z in
        if not (Float.is_nan new_param)  then
          let new_f = Bdd.newvar ctx.man in
          let var_lbl = Bdd.topvar new_f in
          let new_z = cur_z -. param in
          Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.new_param, new_param);
          Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "i%f" param);
          (List.append cur_l [new_f], new_z)
        else
          (List.append cur_l [Bdd.dfalse ctx.man], cur_z)
      ) in
    (* convert the flip list into logical formulae *)
    let (l', _) = List.fold bdd_l ~init:([], Bdd.dtrue ctx.man) ~f:(fun (cur_l, cur_guard) flip ->
        let new_guard = Bdd.dand (Bdd.dnot flip) cur_guard in
        let cur_bdd = Bdd.dand cur_guard flip in
        (List.append cur_l [cur_bdd], new_guard)
      ) in
    (Leaf(IntLeaf(l')), Bdd.dtrue ctx.man)
  | Int(sz, value) ->
    let l = List.init sz (fun i ->
        if i = value then Bdd.dtrue ctx.man else Bdd.dfalse ctx.man) in
    (Leaf(IntLeaf(l)), Bdd.dtrue ctx.man)
  | Eq(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let l1 = extract_discrete v1 and l2 = extract_discrete v2 in
    let zipped = try List.zip_exn l1 l2
            with _ -> failwith (Format.sprintf "Type error: length mismatch between %s and %s"
                                  (string_of_expr e1) (string_of_expr e2)) in
    let bdd = List.fold zipped ~init:(Bdd.dtrue ctx.man) ~f:(fun acc (l, r) ->
        Bdd.dand acc (Bdd.eq l r)
      ) in
    (Leaf(BddLeaf(bdd)), Bdd.dand z1 z2)
  | Plus(e1, e2) ->
    let (v1, z1) = compile_expr ctx env e1 in
    let (v2, z2) = compile_expr ctx env e2 in
    let l1 = extract_discrete v1 and l2 = extract_discrete v2 in
    assert (List.length l1 = List.length l2);
    let len = List.length l1 in
    let init_l = Array.init len ~f:(fun _ -> Bdd.dfalse ctx.man) in
    let _ =List.mapi l1 ~f:(fun outer_i outer_itm ->
        let _ = List.mapi l2 ~f:(fun inner_i inner_itm ->
            let cur_pos = ((outer_i + inner_i) mod len) in
            let cur_arrv = Array.get init_l cur_pos in
            Array.set init_l cur_pos (Bdd.dor cur_arrv (Bdd.dand inner_itm outer_itm));
          ) in ()
      ) in
    (Leaf(IntLeaf(Array.to_list init_l)), Bdd.dtrue ctx.man)
  | FuncCall(c) -> failwith "not impl"

let get_prob e =
  let ctx = new_context () in
  let env = Map.Poly.empty in
  let (v, zbdd) = compile_expr ctx env e in
  let z = Wmc.wmc zbdd ctx.weights in
  let prob = Wmc.wmc (Bdd.dand (extract_bdd v) zbdd) ctx.weights in
  (* BddUtil.dump_dot ctx.name_map (extract_bdd v); *)
  prob /. z

let print_discrete e =
  let ctx = new_context () in
  let env = Map.Poly.empty in
  let (v, zbdd) = compile_expr ctx env e in
  let discrete = extract_discrete v in
  let z = Wmc.wmc zbdd ctx.weights in
  let _ = List.mapi discrete ~f:(fun i itm ->
      let prob = Wmc.wmc (Bdd.dand itm zbdd) ctx.weights in
      Format.printf "%d\t%f\n" i (prob /. z);
    ) in ()
  (* BddUtil.dump_dot ctx.name_map (extract_bdd v); *)
  (* prob /. z *)

(** prints the joint probability distribution as a TSV *)
(* let print_table e =
 *   let ctx = new_context () in
 *   let env = Map.Poly.empty in
 *   let (v, zbdd) = compile_expr ctx env e in
 *   let z = Wmc.wmc zbdd ctx.weights in
 *   (\* let prob = Wmc.wmc (Bdd.dand (extract_bdd v) zbdd) ctx.weights in *\)
 *   (\* prob /. z *\)
 *   let rec print_h (state: varstate btree) (cur_str: String.t) =
 *     match state with
 *     | Leaf(BddLeaf(bdd)) ->  *)
