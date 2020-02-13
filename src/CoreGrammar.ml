open Core
open Cudd
open Wmc
open BddUtil
open VarState

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
  | Lt of expr * expr
  | Int of int * int  (* sz, v *)
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Div of expr * expr
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
  (Float.compare (Float.abs (x -. y)) 0.000001) < 0
  (* Float.abs  < 0.000001 *)

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
  | Neq(e1, e2) -> from_external_expr(Not(Eq(e1, e2)))
  | Minus(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Minus(s1, s2)
  | Mult(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Mult(s1, s2)
  | Div(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Div(s1, s2)
  | Lt(e1, e2) ->
    let s1 = from_external_expr e1 in
    let s2 = from_external_expr e2 in Lt(s1, s2)
  | Lte(e1, e2) -> from_external_expr(Or(Lt(e1, e2), Eq(e1, e2)))
  | Gt(e1, e2) -> from_external_expr(Not(Lte(e1, e2)))
  | Gte(e1, e2) -> from_external_expr(Not(Lt(e1, e2)))
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

let rec from_external_func (f: ExternalGrammar.func) : func =
  {name = f.name; args = f.args; body = from_external_expr f.body}

let rec from_external_prog (p: ExternalGrammar.program) : program =
  {functions = List.map p.functions ~f:from_external_func; body = from_external_expr p.body}


(** Result of compiling an expression *)
type compiled_expr = {
  state: varstate btree;
  z: Bdd.dt;
  flips: Bdd.dt List.t}

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

type compiled_program = {
  ctx: compile_context;
  body: compiled_expr;
}

type env = (String.t, varstate btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let new_context () =
  let man = Man.make_d () in
  Man.disable_autodyn man;
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man = man;
   name_map = names;
   weights = weights;
   funcs = Hashtbl.Poly.create ()}

let rec compile_expr (ctx: compile_context) (env: env) e : compiled_expr =
  (** helper function for implementing binary operations
      [op] : size -> a -> b -> pos, defines the binary operation being implemented *)
  let binop_helper e1 e2 (op: int -> int -> int -> int) =
    let c1 = compile_expr ctx env e1 in
    let c2 = compile_expr ctx env e2 in
    let l1 = extract_discrete c1.state and l2 = extract_discrete c2.state in
    (if (List.length l1 <> List.length l2) then
        failwith (Format.sprintf "Type error: '%s' and '%s' are different types." (string_of_expr e1) (string_of_expr e2)));
    let len = List.length l1 in
    let init_l = Array.init len ~f:(fun _ -> Bdd.dfalse ctx.man) in
    List.iteri l1 ~f:(fun outer_i outer_itm ->
        List.iteri l2 ~f:(fun inner_i inner_itm ->
            let cur_pos = op len outer_i inner_i in
            let cur_arrv = Array.get init_l cur_pos in
            Array.set init_l cur_pos (Bdd.dor cur_arrv (Bdd.dand inner_itm outer_itm));
          ));
    {state=Leaf(IntLeaf(Array.to_list init_l)); z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips} in
  let r = match e with
    | And(e1, e2) ->
      (* and is left-associative, so it prefers this *)
      let c2 = compile_expr ctx env e2 in
      let c1 = compile_expr ctx env e1 in
      let v = Leaf(BddLeaf(Bdd.dand (extract_bdd c1.state) (extract_bdd c2.state))) in
      let z = Bdd.dand c1.z c2.z in
      {state=v; z=z; flips=List.append c1.flips c2.flips}

    | Or(e1, e2) ->
      let c2 = compile_expr ctx env e2 in
      let c1 = compile_expr ctx env e1 in
      let v = Leaf(BddLeaf(Bdd.dor (extract_bdd c1.state) (extract_bdd c2.state))) in
      let z = Bdd.dand c1.z c2.z in
      {state=v; z=z; flips=List.append c1.flips c2.flips}

    | Not(e) ->
      let c = compile_expr ctx env e in
      let v = Bdd.dnot (extract_bdd c.state) in
      {state=Leaf(BddLeaf(v)); z=c.z; flips=c.flips}

    | True -> {state=Leaf(BddLeaf(Bdd.dtrue ctx.man)); z=Bdd.dtrue ctx.man; flips=[]}

    | False -> {state=Leaf(BddLeaf(Bdd.dfalse ctx.man)); z=Bdd.dtrue ctx.man; flips=[]}

    | Ident(s) ->
      (match Map.Poly.find env s with
       | Some(r) -> {state=r; z=Bdd.dtrue ctx.man; flips=[]}
       | _ -> failwith (sprintf "Could not find variable '%s'" s))

    | Tup(e1, e2) ->
      let c1 = compile_expr ctx env e1 in
      let c2 = compile_expr ctx env e2 in
      {state=Node(c1.state, c2.state); z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips}

    | Ite(g, thn, els) ->
      let cthn = compile_expr ctx env thn in
      let cels = compile_expr ctx env els in
      let cg = compile_expr ctx env g in
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
      {state=v'; z=z'; flips = List.append cg.flips (List.append cthn.flips cels.flips)}

    | Fst(e) ->
      let c = compile_expr ctx env e in
      let v' = (match c.state with
          | Node(l, _) -> l
          | _ -> failwith "calling `fst` on non-tuple") in
      {state=v'; z=c.z; flips=c.flips}

    | Snd(e) ->
      let c = compile_expr ctx env e in
      let v' = (match c.state with
          | Node(_, r) -> r
          | _ -> failwith "calling `snd` on non-tuple") in
      {state=v'; z=c.z; flips=c.flips}

    | Flip(f) ->
      let new_f = Bdd.newvar ctx.man in
      let var_lbl = Bdd.topvar new_f in
      Hashtbl.Poly.add_exn ctx.weights var_lbl (1.0-.f, f);
      Hashtbl.add_exn ctx.name_map var_lbl (Format.sprintf "f%f" f);
      {state=Leaf(BddLeaf(new_f)); z=Bdd.dtrue ctx.man; flips=[new_f]}

    | Observe(g) ->
      let c = compile_expr ctx env g in
      {state=Leaf(BddLeaf(Bdd.dtrue ctx.man)); z=Bdd.dand (extract_bdd c.state) c.z; flips=c.flips}

    | Let(x, e1, e2) ->
      let c1 = compile_expr ctx env e1 in
      let env' = Map.Poly.set env ~key:x ~data:c1.state in
      (* Format.printf "Added size %d to table\n" (VarState.state_size [c1.state]); *)
      let c2 = compile_expr ctx env' e2 in
      {state=c2.state; z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips}

    | Discrete(l) ->
      (* first construct a list of all the properly parameterized flips *)
      let flips = ref [] in
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
             flips := List.append !flips [new_f];
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
      {state=Leaf(IntLeaf(l')); z=Bdd.dtrue ctx.man; flips = !flips}

    | Int(sz, value) ->
      let l = List.init sz (fun i ->
          if i = value then Bdd.dtrue ctx.man else Bdd.dfalse ctx.man) in
      {state=Leaf(IntLeaf(l)); z=Bdd.dtrue ctx.man; flips=[]}

    | Eq(e1, e2) ->
      let c1 = compile_expr ctx env e1 in
      let c2 = compile_expr ctx env e2 in
      let l1 = extract_discrete c1.state and l2 = extract_discrete c2.state in
      let zipped = try List.zip_exn l1 l2
        with _ -> failwith (Format.sprintf "Type error: length mismatch between %s and %s"
                              (string_of_expr e1) (string_of_expr e2)) in
      let bdd = List.fold zipped ~init:(Bdd.dfalse ctx.man) ~f:(fun acc (l, r) ->
          Bdd.dor acc (Bdd.dand l r)
        ) in
      {state=Leaf(BddLeaf(bdd)); z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips}

    | Lt(e1, e2) ->
      let c1 = compile_expr ctx env e1 in
      let c2 = compile_expr ctx env e2 in
      let l1 = extract_discrete c1.state and l2 = extract_discrete c2.state in
      let cur = ref (Bdd.dfalse ctx.man) in
      List.iteri l1 ~f:(fun o_idx o_bdd ->
          List.iteri l2 ~f:(fun i_idx i_bdd ->
              if o_idx < i_idx then cur := Bdd.dor !cur (Bdd.dand o_bdd i_bdd) else ();
            ));
      {state=Leaf(BddLeaf(!cur)); z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips}

    | Plus(e1, e2) -> binop_helper e1 e2 (fun sz a b -> (a + b) mod sz)
    | Minus(e1, e2) -> binop_helper e1 e2 (fun sz a b -> abs ((a - b) mod sz))
    | Mult(e1, e2) -> binop_helper e1 e2 (fun sz a b -> ((a * b) mod sz))
    | Div(e1, e2) -> binop_helper e1 e2 (fun sz a b -> (a / b))

    | FuncCall(name, args) ->
      let func = try Hashtbl.Poly.find_exn ctx.funcs name
        with _ -> failwith (Format.sprintf "Could not find function '%s'." name) in
      let cargs = List.map args ~f:(compile_expr ctx env) in
      let zippedargs = try List.zip_exn cargs func.args
        with _ -> failwith (Format.sprintf "Incorrect number of arguments for function call '%s'\n" (string_of_expr e)) in
      (* set up the flip refreshing permutation *)
      let new_flips = List.map func.body.flips ~f:(fun f ->
          let newv = Bdd.newvar ctx.man in
          let lvl = Bdd.topvar newv in
          (match Hashtbl.Poly.find ctx.weights (Bdd.topvar f) with
           | Some(v) -> Hashtbl.Poly.add_exn ctx.weights lvl v
           | None -> ());
          newv) in
      let swapA = List.to_array (List.map new_flips ~f:(fun cur -> Bdd.topvar cur)) in
      let swapB = List.to_array (List.map func.body.flips ~f:(fun cur -> Bdd.topvar cur)) in
      let refreshed_state = map_bddtree func.body.state (fun bdd -> Bdd.swapvariables bdd swapA swapB) in
      let refreshed_z = Bdd.swapvariables func.body.z swapA swapB in
      let argcube = List.fold func.args ~init:(Bdd.dtrue ctx.man) ~f:(fun acc argstate ->
          fold_bddtree argstate acc (fun acc i -> Bdd.dand acc i)) in
      let argiff = List.fold ~init:(Bdd.dtrue ctx.man) zippedargs ~f:(fun acc (carg, placeholder) ->
          let tree = map_tree (zip_tree carg.state placeholder) (function
              | (BddLeaf(a), BddLeaf(p)) ->
                BddLeaf(Bdd.dand acc (Bdd.eq a p))
              | (IntLeaf(al), IntLeaf(pl)) when (List.length al) = (List.length pl) ->
                BddLeaf(List.fold ~init:acc (List.zip_exn al pl) ~f:(fun acc (a, p) ->
                    Bdd.dand acc (Bdd.eq a p)))
              | _ -> failwith (Format.sprintf "Type mismatch in arguments for '%s'\n" (string_of_expr e))) in
          fold_bddtree tree acc (fun acc i -> Bdd.dand acc i)) in
      (* apply the arguments*)
      let final_state = map_bddtree refreshed_state (fun bdd ->
          Bdd.existand argcube argiff bdd) in
      let final_z = List.fold ~init:(Bdd.existand argcube argiff refreshed_z) cargs
          ~f:(fun acc arg -> Bdd.dand arg.z acc ) in
      {state=final_state; z=final_z; flips=new_flips} in
  (* Format.printf "Compiled %s, Size: %d, #live: %d\n"
   *   (string_of_expr e) (VarState.state_size [r.state]) (Man.get_node_count ctx.man); *)
  (* Format.printf "Size: %d\n"
   *   (VarState.state_size [r.state]); *)
  r


(** generates a symbolic representation for a variable of the given type *)
let rec gen_sym_type ctx (t:ExternalGrammar.typ) : varstate btree =
  match t with
  | ExternalGrammar.TBool ->
    let bdd = Bdd.newvar ctx.man in Leaf(BddLeaf(bdd))
  | ExternalGrammar.TInt(sz) ->
    let bdds = List.init sz (fun i -> Bdd.newvar ctx.man) in
    Leaf(IntLeaf(bdds))
  | ExternalGrammar.TTuple(t1, t2) ->
    let s1 = gen_sym_type ctx t1 and s2 = gen_sym_type ctx t2 in
    Node(s1, s2)

let compile_func ctx (f: func) : compiled_func =
  (* set up the context; need both a list and a map, so build both together *)
  let (args, env) = List.fold f.args ~init:([], Map.Poly.empty)
      ~f:(fun (lst, map) (name, typ) ->
          let placeholder_arg = gen_sym_type ctx typ in
          (* the environment must know about the mutual exclusivity of integer arguments
             in order to avoid exponential explosions *)
          let env_arg = map_tree placeholder_arg (function
              | BddLeaf(bdd) -> BddLeaf(bdd)
              | IntLeaf(l) ->
                IntLeaf(List.init (List.length l) (fun i ->
                    List.foldi l ~init:(Bdd.dtrue ctx.man) ~f:(fun idx acc cur ->
                        let bdd = if idx = i then cur else Bdd.dnot cur in
                        Bdd.dand bdd acc
                      )))) in
          let map' = try Map.Poly.add_exn map ~key:name ~data:env_arg
            with _ -> failwith (Format.sprintf "Argument names must be unique: %s found twice" name) in
          (List.append lst [placeholder_arg], map')
        ) in
  (* now compile the function body with these arguments *)
  let body = compile_expr ctx env f.body in
  {args = args; body = body}

let compile_program (p:program) : compiled_program =
  (* Format.printf "Compiling program\n";
   * flush_all (); *)
  (* first compile the functions in topological order *)
  let ctx = new_context () in
  List.iter p.functions ~f:(fun func ->
      let c = compile_func ctx func in
      try Hashtbl.Poly.add_exn ctx.funcs ~key:func.name ~data:c
      with _ -> failwith (Format.sprintf "Function names must be unique: %s found twice" func.name)
    );
  (* now compile the main body, which is the result of the program *)
  let env = Map.Poly.empty in
  {ctx = ctx; body = compile_expr ctx env p.body}

let get_prob p =
  let c = compile_program p in
  let z = Wmc.wmc c.body.z c.ctx.weights in
  let prob = Wmc.wmc (Bdd.dand (extract_bdd c.body.state) c.body.z) c.ctx.weights in
  prob /. z

let print_discrete p =
  let c = compile_program p in
  let discrete = extract_discrete c.body.state in
  let z = Wmc.wmc c.body.z c.ctx.weights in
  let _ = List.mapi discrete ~f:(fun i itm ->
      let prob = Wmc.wmc (Bdd.dand itm c.body.z) c.ctx.weights in
      Format.printf "%d\t%f\n" i (prob /. z);
    ) in ()

(** prints the joint probability distribution as a TSV *)
let get_table p =
  let r = compile_program p in
  let zbdd = r.body.z in
  let z = Wmc.wmc zbdd r.ctx.weights in
  let rec process_state state =
    match state with
    | Leaf(BddLeaf(bdd)) ->
      [(True, bdd); (False, Bdd.dnot bdd)]
    | Leaf(IntLeaf(l)) ->
      List.mapi l ~f:(fun i itm ->
          ((Int(List.length l, i)), itm)
        )
    | Node(l, r) ->
      let lst = process_state l and rst = process_state r in
      List.map lst ~f:(fun (lt, lbdd) ->
          List.map rst ~f:(fun (rt, rbdd) ->
              (Tup(lt, rt), Bdd.dand lbdd rbdd)
            )
        )
      |> List.concat in
  let states = process_state r.body.state in
  (* convert the state list into probabilities *)
  List.map states ~f:(fun (label, bdd) ->
      let prob = (Wmc.wmc (Bdd.dand bdd zbdd) r.ctx.weights) /. z in
      (label, prob))
