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
  | FuncCall of String.t * expr List.t
  | Observe of expr
[@@deriving sexp_of]
and fcall = {
  fname: String.t;
  args: expr
}
[@@deriving sexp_of]


let rec string_of_expr e =
  Sexp.to_string_hum (sexp_of_expr e)

(** Core function grammar *)
type func = {
  name: String.t;
  args: ExternalGrammar.arg List.t;
  body: expr;
}
[@@deriving sexp_of]


type program = {
  functions: func List.t;
  body: expr;
}
[@@deriving sexp_of]

let within_epsilon x y =
  Float.abs (x -. y) < 0.000001

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
  | FuncCall(id, args) -> FuncCall(id, List.map args ~f:(fun i -> from_external_expr i))


(** The result of compiling an expression. A pair (value, normalizing constant) *)
type varstate =
    BddLeaf of Bdd.dt
  | IntLeaf of Bdd.dt List.t

(** A compiled variable. It is a tree to compile tuples. *)
type 'a btree =
    Leaf of 'a
  | Node of 'a btree * 'a btree
[@@deriving sexp]

let extract_bdd (state: varstate btree) =
  match state with
  | Leaf(BddLeaf(bdd)) -> bdd
  | _ -> failwith "invalid bdd extraction"

let extract_discrete(state: varstate btree) =
  match state with
  | Leaf(IntLeaf(l)) -> l
  | _ -> failwith "invalid bdd extraction"

(** applies `f` to each leaf in `s` *)
let rec map_tree (s:'a btree) (f: 'a -> 'b) : 'b btree =
  match s with
  | Leaf(bdd) -> Leaf(f bdd)
  | Node(l, r) -> Node(map_tree l f, map_tree r f)

(** Applies `f` to each BDD in `s` *)
let rec map_bddtree (s:varstate btree) (f: Bdd.dt -> Bdd.dt) : varstate btree =
  match s with
  | Leaf(BddLeaf(bdd)) -> Leaf(BddLeaf(f bdd))
  | Leaf(IntLeaf(l)) -> Leaf(IntLeaf(List.map l ~f:f))
  | Node(l, r) -> Node(map_bddtree l f, map_bddtree r f)


let rec zip_tree (s1: 'a btree) (s2: 'b btree) =
  match (s1, s2) with
  | (Leaf(a), Leaf(b)) -> Leaf((a, b))
  | (Node(a_l, a_r), Node(b_l, b_r)) ->
    Node(zip_tree a_l b_l, zip_tree a_r b_r)
  | _ -> failwith "could not zip trees, incompatible shape"


(** Result of compiling an expression *)
type compiled_expr = {state: varstate btree; z: Bdd.dt;}

type compiled_func = {
  args: (varstate btree) List.t;
  body: compiled_expr;
}

type compile_context = {
  man: Man.dt;
  name_map: (int, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
  funcs: (String.t, compiled_func) Hashtbl.Poly.t;
}

type env = (String.t, varstate btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let new_context () =
  let man = Man.make_d () in
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man = man;
   name_map = names;
   weights = weights;
   funcs = Hashtbl.Poly.create ()}

let rec compile_expr (ctx: compile_context) (env: env) e : compiled_expr =
  match e with
  | And(e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    let v = Leaf(BddLeaf(Bdd.dand (extract_bdd c1.state) (extract_bdd c2.state))) in
    let z = Bdd.dand c1.z c2.z in
    {state=v; z=z;}

  | Or(e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    let v = Leaf(BddLeaf(Bdd.dor (extract_bdd c1.state) (extract_bdd c2.state))) in
    let z = Bdd.dand c1.z c2.z in
    {state=v; z=z}

  | Not(e) ->
    let c = compile_expr ctx env e in
    let v = Bdd.dnot (extract_bdd c.state) in
    {state=Leaf(BddLeaf(v)); z=c.z}

  | True -> {state=Leaf(BddLeaf(Bdd.dtrue ctx.man)); z=Bdd.dtrue ctx.man}

  | False -> {state=Leaf(BddLeaf(Bdd.dfalse ctx.man)); z=Bdd.dtrue ctx.man}

  | Ident(s) ->
    (match Map.Poly.find env s with
     | Some(r) -> {state=r; z=Bdd.dtrue ctx.man}
     | _ -> failwith (sprintf "Could not find Boolean variable %s" s))

  | Tup(e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    {state=Node(c1.state, c2.state); z=Bdd.dand c1.z c2.z}

  | Ite(g, thn, els) ->
    let cg = compile_expr ctx env g in
    let cthn = compile_expr ctx env thn in
    let cels = compile_expr ctx env els in
    let gbdd = extract_bdd cg.state in
    let zipped = zip_tree cthn.state cels.state in
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
    let z' = Bdd.dand cg.z (Bdd.dor (Bdd.dand cthn.z gbdd)
                              (Bdd.dand cels.z (Bdd.dnot gbdd))) in
    {state=v'; z=z'}

  | Fst(e) ->
    let c = compile_expr ctx env e in
    let v' = (match c.state with
     | Node(l, _) -> l
     | _ -> failwith "calling `fst` on non-tuple") in
    {state=v'; z=c.z}

  | Snd(e) ->
    let c = compile_expr ctx env e in
    let v' = (match c.state with
     | Node(_, r) -> r
     | _ -> failwith "calling `snd` on non-tuple") in
    {state=v'; z=c.z}

  | Flip(f) ->
    let new_f = Bdd.newvar ctx.man in
    let var_lbl = Bdd.topvar new_f in
    Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.f, f);
    Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "f%f" f);
    {state=Leaf(BddLeaf(new_f)); z=Bdd.dtrue ctx.man}

  | Observe(g) ->
    let c = compile_expr ctx env g in
    {state=Leaf(BddLeaf(Bdd.dtrue ctx.man)); z=Bdd.dand (extract_bdd c.state) c.z}

  | Let(x, e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let env' = Map.Poly.set env ~key:x ~data:c1.state in
    let c2 = compile_expr ctx env' e2 in
    {state=c2.state; z=Bdd.dand c1.z c2.z}

  | Discrete(l) ->
    (* first construct a list of all the properly parameterized flips *)
    let (bdd_l, _) = List.fold ~init:([], 1.0) l ~f:(fun (cur_l, cur_z) param ->
        let new_param = param /. cur_z in
        (* optimize: remove unnecessary flips if they are constant parameters *)
        (match new_param with
         | x when Float.is_nan new_param || within_epsilon new_param 0.0 ->
           List.append cur_l [Bdd.dfalse ctx.man], cur_z
         | x when within_epsilon new_param 1.0 ->
           List.append cur_l [Bdd.dtrue ctx.man], cur_z
         | _ ->
          let new_f = Bdd.newvar ctx.man in
          let var_lbl = Bdd.topvar new_f in
          let new_z = cur_z -. param in
          Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.new_param, new_param);
          Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "i%f" param);
          (List.append cur_l [new_f], new_z))
      ) in
    (* convert the flip list into logical formulae *)
    let (l', _) = List.fold bdd_l ~init:([], Bdd.dtrue ctx.man) ~f:(fun (cur_l, cur_guard) flip ->
        let new_guard = Bdd.dand (Bdd.dnot flip) cur_guard in
        let cur_bdd = Bdd.dand cur_guard flip in
        (List.append cur_l [cur_bdd], new_guard)
      ) in
    {state=Leaf(IntLeaf(l')); z=Bdd.dtrue ctx.man}

  | Int(sz, value) ->
    let l = List.init sz (fun i ->
        if i = value then Bdd.dtrue ctx.man else Bdd.dfalse ctx.man) in
    {state=Leaf(IntLeaf(l)); z=Bdd.dtrue ctx.man}
  | Eq(e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    let l1 = extract_discrete c1.state and l2 = extract_discrete c2.state in
    let zipped = try List.zip_exn l1 l2
            with _ -> failwith (Format.sprintf "Type error: length mismatch between %s and %s"
                                  (string_of_expr e1) (string_of_expr e2)) in
    let bdd = List.fold zipped ~init:(Bdd.dtrue ctx.man) ~f:(fun acc (l, r) ->
        Bdd.dand acc (Bdd.eq l r)
      ) in
    {state=Leaf(BddLeaf(bdd)); z=Bdd.dand c1.z c2.z}

  | Plus(e1, e2) ->
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    let l1 = extract_discrete c1.state and l2 = extract_discrete c2.state in
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
    {state=Leaf(IntLeaf(Array.to_list init_l)); z=Bdd.dtrue ctx.man}

  | FuncCall(name, args) ->
    let cargs = List.map args ~f:(compile_expr ctx env) in
    let func = try Hashtbl.Poly.find_exn ctx.funcs name
      with _ -> failwith (Format.sprintf "Could not find function '%s'." name) in
    (** 1. refresh the flips *)
    let nvmap = Hashtbl.Poly.create () (* map from old to new variable labels *) in
    let visitedmap = Hashtbl.Poly.create () (* caches the visited states for traversing the BDD *) in
    (* helper function: traverses the BDD and generates a copy BDD with all new variables *)
    (* in the future it would probably make sense to make this method native *)
    let rec refresh_flips (bdd: Bdd.dt) : Bdd.dt =
      Hashtbl.Poly.find_or_add visitedmap bdd ~default:(fun () ->
          (match Bdd.inspect bdd with
           | Bdd.Bool(true) -> Bdd.dtrue ctx.man
           | Bdd.Bool(false) -> Bdd.dfalse ctx.man
           | Bdd.Ite(lvl, thn, els) ->
             let root = Hashtbl.Poly.find_or_add nvmap lvl ~default:(fun () -> Bdd.newvar ctx.man) in
             let s1 = refresh_flips thn and s2 = refresh_flips els in
             Bdd.ite root s1 s2)) in
    let refreshed_state = ref (map_tree func.body.state (fun itm ->
        match itm with
        | BddLeaf(bdd) -> BddLeaf(refresh_flips bdd)
        | IntLeaf(i) -> IntLeaf(List.map i ~f:refresh_flips))) in
    let refreshed_z = refresh_flips func.body.z in
    (** 2. substitute in the arguments *)
    (* for each compiled argument, update the refreshed state by substituting
       its argument variables *)
    let zipped = try List.zip_exn cargs func.args
      with _ -> failwith (Format.sprintf "Incorrect number of arguments for function call '%s'\n" (string_of_expr e)) in
    List.iter zipped ~f:(fun (carg, placeholder) ->
        let _ = map_tree (zip_tree carg.state placeholder) (function
            | (BddLeaf(a), BddLeaf(p)) ->
              let subst_p = Hashtbl.Poly.find_exn nvmap (Bdd.topvar p) in
              refreshed_state := map_bddtree !refreshed_state (fun c -> Bdd.compose (Bdd.topvar subst_p) a c);
            | (IntLeaf(al), IntLeaf(pl)) -> failwith ""
            | _ -> failwith (Format.sprintf "Type mismatch in arguments for '%s'\n" (string_of_expr e))
          ) in ()
      );
    let new_z = List.fold cargs ~init:refreshed_z ~f:(fun acc i -> Bdd.dand acc i.z) in
    {state = !refreshed_state; z=new_z}


(** generates a symbolic representation for a variable of the given type *)
let rec gen_sym_type ctx (t:ExternalGrammar.typ) : varstate btree =
  match t with
  | ExternalGrammar.TBool ->
    let bdd = Bdd.newvar ctx.man in Leaf(BddLeaf(bdd))
  | ExternalGrammar.TInt(sz) ->
    let lst = List.init sz (fun i -> Bdd.newvar ctx.man) in
    Leaf(IntLeaf(lst))
  | ExternalGrammar.TTuple(t1, t2) ->
    let s1 = gen_sym_type ctx t1 and s2 = gen_sym_type ctx t2 in
    Node(s1, s2)

let compile_func ctx (f: func) : compiled_func =
  (* set up the context; need both a list and a map, so build both together *)
  let (args, env) = List.fold f.args ~init:([], Map.Poly.empty)
      ~f:(fun (lst, map) (name, typ) ->
          let arg = gen_sym_type ctx typ in
          let map' = try Map.Poly.add_exn map ~key:name ~data:arg
            with _ -> failwith (Format.sprintf "Argument names must be unique: %s found twice" name) in
          (List.append lst [arg], map')
        ) in
  (* now compile the function body with these arguments *)
  let body = compile_expr ctx env f.body in
  {args = args; body = body}

let compile_program (p:program) : compiled_expr =
  (* first compile the functions in topological order *)
  let ctx = new_context () in
  List.iter p.functions ~f:(fun func ->
      let c = compile_func ctx func in
      try Hashtbl.Poly.add_exn ctx.funcs ~key:func.name ~data:c
      with _ -> failwith (Format.sprintf "Function names must be unique: %s found twice" func.name)
    );
  (* now compile the main body, which is the result of the program *)
  let env = Map.Poly.empty in
  compile_expr ctx env p.body

let get_prob e =
  let ctx = new_context () in
  let env = Map.Poly.empty in
  let c = compile_expr ctx env e in
  let z = Wmc.wmc c.z ctx.weights in
  let prob = Wmc.wmc (Bdd.dand (extract_bdd c.state) c.z) ctx.weights in
  (* BddUtil.dump_dot ctx.name_map (extract_bdd v); *)
  prob /. z

let print_discrete e =
  let ctx = new_context () in
  let env = Map.Poly.empty in
  let c = compile_expr ctx env e in
  let discrete = extract_discrete c.state in
  let z = Wmc.wmc c.z ctx.weights in
  let _ = List.mapi discrete ~f:(fun i itm ->
      let prob = Wmc.wmc (Bdd.dand itm c.z) ctx.weights in
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
