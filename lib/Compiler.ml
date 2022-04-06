open Core
open Wmc
open VarState
module CG = CoreGrammar
open Bdd
module LF = LogicalFormula

let flip_id = ref 1

(** Result of compiling an expression *)
type compiled_expr = {
  state: bddptr btree;
  z: bddptr;
  flips: bddptr List.t}

type compiled_func = {
  args: (bddptr btree) List.t;
  body: compiled_expr;
}

type compile_context = {
  man: Bdd.manager;
  name_map: (label, String.t) Hashtbl.Poly.t; (* map from variable identifiers to names, for debugging *)
  weights: weight; (* map from variables to weights *)
  eager_eval: bool; (* true if eager let evaluation *)
  funcs: (String.t, compiled_func) Hashtbl.Poly.t;
}

type compiled_program = {
  ctx: compile_context;
  body: compiled_expr;
}

type env = (String.t, bddptr btree) Map.Poly.t (* map from variable identifiers to BDDs*)

let ctx_man = mk_bdd_manager_default_order 1

let new_context ~eager_eval () =
  let man = ctx_man in
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man = man;
   name_map = names;
   weights = weights;
   funcs = Hashtbl.Poly.create ();
   eager_eval = eager_eval}

(** generates a symbolic representation for a variable of the given type *)
let rec gen_sym_type ctx (t:CG.typ) : bddptr btree =
  match t with
  | TBool ->
    let bdd = bdd_newvar ctx true in Leaf(bdd)
  | TTuple(t1, t2) ->
    let s1 = gen_sym_type ctx t1 and s2 = gen_sym_type ctx t2 in
    Node(s1, s2)

let rec is_const mgr (st: bddptr btree) =
  match st with
  | Leaf(v) -> Bdd.bdd_is_const mgr v
  | Node(l, r) -> (is_const mgr l) && (is_const mgr r)

let rec compile_expr (ctx: compile_context) (tenv: CG.tenv) (env: env) (e : CG.expr) : compiled_expr =
  let binop_helper f e1 e2 =
    let c1 = compile_expr ctx tenv env e1 in
    let c2 = compile_expr ctx tenv env e2 in
    let v = Leaf(f ctx.man (extract_leaf c1.state) (extract_leaf c2.state)) in
    let z = Bdd.bdd_and ctx.man c1.z c2.z in
    {state=v; z=z; flips=c1.flips @ c2.flips} in

  let r = match e with
  | And(e1, e2) -> binop_helper Bdd.bdd_and e1 e2
  | Or(e1, e2) -> binop_helper Bdd.bdd_or e1 e2
  | Xor(e1, e2) -> binop_helper Bdd.bdd_xor e1 e2
  | Eq(e1, e2) -> binop_helper Bdd.bdd_iff e1 e2
  | Not(e) ->
    let c = compile_expr ctx tenv env e in
    let v = Bdd.bdd_negate ctx.man (extract_leaf c.state) in
    {state=Leaf(v); z=c.z; flips=c.flips}

  | True -> {state=Leaf(Bdd.bdd_true ctx.man); z=Bdd.bdd_true ctx.man; flips=[]}

  | False -> {state=Leaf(Bdd.bdd_false ctx.man); z=Bdd.bdd_true ctx.man; flips=[]}

  | Ident(s) ->
    (match Map.Poly.find env s with
     | Some(r) -> {state=r; z=Bdd.bdd_true ctx.man; flips=[]}
     | _ -> failwith (sprintf "Could not find variable '%s'" s))

  | Tup(e1, e2) ->
    let c1 = compile_expr ctx tenv env e1 in
    let c2 = compile_expr ctx tenv env e2 in
    {state=Node(c1.state, c2.state); z=Bdd.bdd_and ctx.man c1.z c2.z; flips=c1.flips @ c2.flips}

  | Ite(g, thn, els) ->
    let cg = compile_expr ctx tenv env g in
    if is_const ctx.man cg.state then
      let v = extract_leaf cg.state in
      let r = compile_expr ctx tenv env (if Bdd.bdd_is_true ctx.man v then thn else els) in
      {state=r.state; z=Bdd.bdd_and ctx.man cg.z r.z; flips = cg.flips @ r.flips}
    else
      let cthn = compile_expr ctx tenv env thn in
      let cels = compile_expr ctx tenv env els in
      let gbdd = extract_leaf cg.state in
      let zipped = zip_tree cthn.state cels.state in
      let v' = map_tree zipped (fun (thn_state, els_state) ->
          Bdd.bdd_ite ctx.man gbdd thn_state els_state
        ) in
      let z' = Bdd.bdd_and ctx.man cg.z (Bdd.bdd_ite ctx.man gbdd cthn.z cels.z) in
      {state=v'; z=z'; flips = cg.flips @ cthn.flips @ cels.flips}

  | Fst(e) ->
    let c = compile_expr ctx tenv env e in
    let v' = (match c.state with
     | Node(l, _) -> l
     | _ -> failwith (Format.sprintf "Internal Failure: calling `fst` on non-tuple at %s" (CG.string_of_expr e))) in
    {state=v'; z=c.z; flips=c.flips}

  | Snd(e) ->
    let c = compile_expr ctx tenv env e in
    let v' = (match c.state with
     | Node(_, r) -> r
     | _ -> failwith (Format.sprintf "Internal Failure: calling `snd` on non-tuple at %s" (CG.string_of_expr e))) in
    {state=v'; z=c.z; flips=c.flips}

  | Flip(f) ->
    let new_f = Bdd.bdd_newvar ctx.man true in
    let var_lbl = Bdd.bdd_topvar ctx.man new_f in
    let var_name = (Format.sprintf "f%d_%s" !flip_id (Bignum.to_string_hum f)) in
    Hashtbl.add_exn ctx.name_map ~key:var_lbl ~data:var_name;
    flip_id := !flip_id + 1;
    Hashtbl.Poly.add_exn ctx.weights ~key:var_lbl ~data:(Bignum.(one-f), f);
    {state=Leaf(new_f); z=Bdd.bdd_true ctx.man; flips=[new_f]}

  | Observe(g) ->
    let c = compile_expr ctx tenv env g in
    {state=Leaf(Bdd.bdd_true ctx.man); z=Bdd.bdd_and ctx.man (extract_leaf c.state) c.z; flips=c.flips}

  | Let(x, e1, e2) ->
    let c1 = compile_expr ctx tenv env e1 in
    let t = (CG.type_of tenv e1) in
    let tenv' = Map.Poly.set tenv ~key:x ~data:t in
    if is_const ctx.man c1.state then (* this value is a heuristic *)
      let env' = Map.Poly.set env ~key:x ~data:c1.state in
      let c2 = compile_expr ctx tenv' env' e2 in
      {state=c2.state; z=Bdd.bdd_and ctx.man c1.z c2.z; flips=List.append c1.flips c2.flips}
    else
      if not ctx.eager_eval then
        (* create a temp variable *)
        let tmp = gen_sym_type ctx.man t in
        let env' = Map.Poly.set env ~key:x ~data:tmp in
        let c2 = compile_expr ctx tenv' env' e2 in
        let final_state = subst_state ctx.man tmp c1.state c2.state in
        let final_z = extract_leaf (subst_state ctx.man tmp c1.state (Leaf(c2.z))) in
        {state=final_state; z=Bdd.bdd_and ctx.man c1.z final_z; flips=c1.flips @ c2.flips}
      else
        (* create a temp variable *)
        let env' = Map.Poly.set env ~key:x ~data:c1.state in
        let c2 = compile_expr ctx tenv' env' e2 in
        {state=c2.state; z=Bdd.bdd_and ctx.man c1.z c2.z; flips=c1.flips @ c2.flips}


  | Sample(e) -> failwith "not implemented"
  (* | Sample(e) ->
   *   let sube = compile_expr ctx tenv env e in
   *   (\* perform sequential sampling *\)
   *   let rec sequential_sample cur_obs state =
   *     (match state with
   *      | Leaf(bdd) ->
   *        let t = Wmc.wmc (Bdd.dand (Bdd.dand cur_obs bdd) sube.z) ctx.weights in
   *        let curz = Wmc.wmc (Bdd.dand sube.z cur_obs) ctx.weights in
   *        let rndvalue = Random.float 1.0 in
   *        if compare_float rndvalue (t /. curz) < 0 then (bdd, Leaf(Bdd.dtrue ctx.man)) else (Bdd.dnot bdd, Leaf(Bdd.dfalse ctx.man))
   *      | Node(l, r) ->
   *        let lbdd, lres = sequential_sample cur_obs l in
   *        let rbdd, rres = sequential_sample lbdd r in
   *        (rbdd, Node(lres, rres))
   *     ) in
   *   let _, r = sequential_sample (Bdd.dtrue ctx.man) sube.state in
   *   {state=r; z=Bdd.dtrue ctx.man; flips=[]} *)

  | FuncCall(name, args) ->
    let func = try Hashtbl.Poly.find_exn ctx.funcs name
      with _ -> failwith (Format.sprintf "Could not find function '%s'." name) in

    let cargs = List.map args ~f:(compile_expr ctx tenv env) in
    (* first refresh all the flips... *)
    let new_flips = List.map func.body.flips ~f:(fun f ->
        let cur_name = Hashtbl.find_exn ctx.name_map (Bdd.bdd_topvar ctx.man f) in
        let var_name = (Format.sprintf "%s_%d" cur_name !flip_id) in
        flip_id := !flip_id + 1;

        let newv = Bdd.bdd_newvar ctx.man true in
        let lvl = Bdd.bdd_topvar ctx.man newv in
        Hashtbl.add_exn ctx.name_map ~key:lvl ~data:var_name;
        (match Hashtbl.Poly.find ctx.weights (Bdd.bdd_topvar ctx.man f) with
         | Some(v) -> Hashtbl.Poly.add_exn ctx.weights ~key:lvl ~data:v
         | None -> ());
        newv) in
    let flip_labels = List.map func.body.flips ~f:(fun cur -> Bdd.bdd_topvar ctx.man cur) in
    let refreshed_state = map_tree func.body.state (fun bdd -> Bdd.bdd_vector_compose ctx.man bdd flip_labels new_flips) in
    let refreshed_z = Bdd.bdd_vector_compose ctx.man func.body.z flip_labels new_flips in

    let argz = List.fold cargs ~init:(Bdd.bdd_true ctx.man) ~f:(fun acc i -> Bdd.bdd_and ctx.man i.z acc) in

    (* now substitute all the arguments in *)
    let argflips = List.fold cargs ~init:[] ~f:(fun acc i -> acc @ i.flips) in
    let zippedargs = (List.zip_exn func.args cargs) in
    let final_state = List.fold ~init:refreshed_state zippedargs ~f:(fun acc (x, c) ->
        subst_state ctx.man x c.state acc
      ) in
    let final_z = List.fold ~init:refreshed_z zippedargs ~f:(fun acc (x, c) ->
        extract_leaf (subst_state ctx.man x c.state (Leaf(acc)))
      ) in
    {state=final_state; z=Bdd.bdd_and ctx.man argz final_z; flips=new_flips @ argflips}
  in
 r

let compile_func (ctx: compile_context) tenv (f: CG.func) : compiled_func =
  (* set up the context; need both a list and a map, so build both together *)
  let new_tenv = List.fold ~init:tenv f.args ~f:(fun acc (name, typ) ->
      Map.Poly.add_exn acc ~key:name ~data:typ
    ) in
  let (args, env) = List.fold f.args ~init:([], Map.Poly.empty)
      ~f:(fun (lst, map) (name, typ) ->
          let placeholder_arg = gen_sym_type ctx.man typ in
          List.iteri (VarState.collect_leaves placeholder_arg) ~f:(fun idx i  ->
              Hashtbl.Poly.add_exn ctx.name_map ~key:(Bdd.bdd_topvar ctx.man i) ~data:(Format.sprintf "%s%d" name idx);
            );
          (lst @ [placeholder_arg], Map.Poly.set map ~key:name ~data:placeholder_arg)
        ) in
  (* now compile the function body with these arguments *)
  let body = compile_expr ctx new_tenv env f.body in
  {args = args; body = body}

let compile_program (p:CG.program) ~eager_eval : compiled_program =
  (* first compile the functions in topological order *)
  let ctx = new_context ~eager_eval () in
  let tenv = ref Map.Poly.empty in
  List.iter p.functions ~f:(fun func ->
      let c = compile_func ctx !tenv func in
      tenv := Map.Poly.add_exn !tenv ~key:func.name ~data:(CG.type_of_fun !tenv func);
      try Hashtbl.Poly.add_exn ctx.funcs ~key:func.name ~data:c
      with _ -> failwith (Format.sprintf "Function names must be unique: %s found twice" func.name)
    );
  (* now compile the main body, which is the result of the program *)
  let env = Map.Poly.empty in
  {ctx = ctx; body = compile_expr ctx !tenv env p.body}

let compile_to_bdd (p: LF.program) : compiled_program = 
  let ctx = new_context false () in
  let env = Hashtbl.Poly.create () in
  let w = p.weights in
  let b = p.binary in
  let e = LF.extract_tup p.body b in
  (* let u = p.unary in *)
  let rec compile_expr_bdd (ctx: compile_context) (e: LF.expr ref) : compiled_expr =
    
    let r = match !e with
      | And(e1, e2) -> 
        (* let _ = match Hashtbl.Poly.find b (e1, e2, And_ind) with
          | None ->
          | Some(n) -> v
        in *)
        let c1 = compile_expr_bdd ctx e1 in
        let c2 = compile_expr_bdd ctx e2 in
        let v = Leaf(Bdd.bdd_and ctx.man (extract_leaf c1.state) (extract_leaf c2.state)) in
        let z = Bdd.bdd_and ctx.man c1.z c2.z in
        {state=v; z=z; flips=c1.flips @ c2.flips}
      | Or(e1, e2) ->
        let c1 = compile_expr_bdd ctx e1 in
        let c2 = compile_expr_bdd ctx e2 in
        let v = Leaf(Bdd.bdd_or ctx.man (extract_leaf c1.state) (extract_leaf c2.state)) in
        let z = Bdd.bdd_and ctx.man c1.z c2.z in
        {state=v; z=z; flips=c1.flips @ c2.flips}
      | Atom(x) ->
        let r = match Hashtbl.Poly.find env x with
        | Some(r) -> {state=r; z=Bdd.bdd_true ctx.man; flips=[]}
        | _ -> 
          let f = try Hashtbl.Poly.find_exn w x 
            with _ -> failwith (Format.sprintf "Could not found flip '%s'." x) in
          let new_f = Bdd.bdd_newvar ctx.man true in
          let var_lbl = Bdd.bdd_topvar ctx.man new_f in
          let var_name = (Format.sprintf "f%d_%s" !flip_id (Bignum.to_string_hum f)) in
          Hashtbl.add_exn ctx.name_map ~key:var_lbl ~data:var_name;
          flip_id := !flip_id + 1;
          Hashtbl.Poly.add_exn ctx.weights ~key:var_lbl ~data:(Bignum.(one-f), f);
          let v = Leaf(new_f) in
          Hashtbl.Poly.add_exn env ~key:x ~data:v;
          {state=v; z=Bdd.bdd_true ctx.man; flips=[new_f]}
        in
        r
      | True ->
        {state=Leaf(Bdd.bdd_true ctx.man); z=Bdd.bdd_true ctx.man; flips=[]}
      | Not(e1) ->
        let c = compile_expr_bdd ctx e1 in
        let v = Bdd.bdd_negate ctx.man (extract_leaf c.state) in
        {state=Leaf(v); z=c.z; flips=c.flips}
      | Tup(e1, e2) ->
        let c1 = compile_expr_bdd ctx e1 in
        let c2 = compile_expr_bdd ctx e2 in
        {state=Node(c1.state, c2.state); z=Bdd.bdd_and ctx.man c1.z c2.z; flips=c1.flips @ c2.flips}
    in
    r
  in
  {ctx = ctx; body = compile_expr_bdd ctx e}

let compile_to_cnf (p: LF.program) t : LF.wcnf =
  let subfx = ref 0 in
  let fresh () =
    subfx := !subfx + 1;
    let x = Format.sprintf "x_%d" !subfx in
    x
  in
  let true_clause = fresh () in

  let cnf_nodes = Hashtbl.Poly.create () in

  (* Generate LF expressions for each row of the table (String.t * LF.expr) list *)
  let gen_neg (x1: String.t) (s1: LF.cnf) =
    let open LogicalFormula in
    let x = fresh() in

    (* !t1 | !x1
        t1 | x1 *)
    let subf_1 = [Neg(x); Neg(x1)] in
    let subf_2 = if String.equal x1 true_clause then [] else [Pos(x); Pos(x1)] in
    
    let subf = subf_1::subf_2::[] in
    x, (subf@s1)
  in

  let gen_and (x1: String.t) (s1: LF.cnf) (x2: String.t) (s2: LF.cnf) =
    let open LogicalFormula in
    let x = fresh() in

    (* !t1 | (x1 & x2) => (!t1 | x1) & (!t1 | x2)
      t1 | !(x1 & x2) => (t1 | !x1 | !x2)  *)
    let subf_1 = if String.equal x1 true_clause then [] else [Neg(x); Pos(x1)] in
    let subf_2 = if String.equal x2 true_clause then [] else [Neg(x); Pos(x2)] in
    let subf_3 = [Pos(x); Neg(x1); Neg(x2)] in
    
    let subf = subf_1::subf_2::subf_3::[] in
    x, (subf@s1@s2)
  in

  let rec gen_subf (e: LF.expr ref) : String.t * LF.cnf =
    let open LogicalFormula in
    
    let def_func = match !e with
      | And(e1, e2) -> 
        (fun () -> 
          let x1, s1 = gen_subf e1 in
          let x2, s2 = gen_subf e2 in
          gen_and x1 s1 x2 s2)
      | Or(e1, e2) -> 
        (fun () -> 
          let x1, s1 = gen_subf e1 in
          let x2, s2 = gen_subf e2 in
          let x = fresh() in

          (* !t1 | (x1 | x2) => (!t1 | x1 | x2)
            t1 | !(x1 | x2) => (t1 | !x1) & (t1 | !x2) *)
          let subf_1 = if (String.equal x1 true_clause) || (String.equal x2 true_clause) then 
            [] else [Neg(x); Pos(x1); Pos(x2)] in
          let subf_2 = [Pos(x); Neg(x1)] in
          let subf_3 = [Pos(x); Neg(x2)] in
          
          let subf = subf_1::subf_2::subf_3::[] in
          x, (subf@s1@s2))
      | Atom(x) -> (fun () -> x, [])
      | True -> (fun () -> true_clause, [[Pos(true_clause)]])
      | Not(e1) -> 
        (fun () -> 
          let x1, s1 = gen_subf e1 in
          gen_neg x1 s1)
      | Tup(e1, e2) -> 
        (fun () -> 
          let tup = ref (And(e1, e2)) in 
          let x1, s1 = gen_subf tup in
          x1, s1)
    in
    let x, subf = Hashtbl.Poly.find_or_add cnf_nodes e ~default:def_func in
    x, subf
  in

  let gen_cnf (x: String.t) (e: LF.cnf) : LF.cnf =
    let open LogicalFormula in

    let t_phi_cnf = [Pos(x)]::e in
    t_phi_cnf
  in

  let rec gen_table (e:LF.expr ref) t = 
    let open ExternalGrammar in
    let open LogicalFormula in    
    match t with
    | TBool -> 
      (match !e with
      | And(_) | Or(_)| Atom(_) | True | Not(_) ->
        let x, s = gen_subf e in
        let x_neg, s_neg = gen_neg x s in
        let pos_cnf = gen_cnf x s in
        let neg_cnf = gen_cnf x_neg s_neg in
        [(`True, x, pos_cnf); (`False, x_neg, neg_cnf)]
      | _ -> failwith "Unreachable")
    | TInt(1) ->
      (match !e with
      | And(_) | Or(_)| Atom(_) | True | Not(_) ->
        let x, s = gen_subf e in
        let x_neg, s_neg = gen_neg x s in
        let pos_cnf = gen_cnf x s in
        let neg_cnf = gen_cnf x_neg s_neg in
        [(`Int(0), x_neg, neg_cnf); (`Int(1), x, pos_cnf)]
      | _ -> failwith "Unreachable")
    | TInt(sz) ->
      let e1, e2 = match !(LF.extract_tup e p.binary) with
      | Tup(e1, e2) -> e1, e2
      | _ -> failwith "Unreachable"
      in 
      let sub1 = gen_table e2 (TInt(sz-1)) in
      let curbitvalue = 1 lsl (sz - 1) in
      let x1, e1_cnf = gen_subf e1 in
      let lower = List.map sub1 ~f:(fun (t, subx, subcnf) ->
          let x1_neg, s1 = gen_neg x1 e1_cnf in
          let and_x, s = gen_and x1_neg s1 subx subcnf in
          let and_cnf = gen_cnf and_x s in

          match t with
            `Int(tval) -> `Int(tval), and_x, and_cnf
          | _ -> failwith "Unreachable"
        ) in
      let upper = List.map sub1 ~f:(fun (t, subx, subcnf) ->
          let and_x, s = gen_and x1 e1_cnf subx subcnf in
          let and_cnf = gen_cnf and_x s in
          
          match t with
            `Int(tval) -> `Int(tval + curbitvalue), and_x, and_cnf
          | _ -> failwith "Unreachable"
        ) in
      lower @ upper
    | TTuple(t1, t2) ->
      (match !e with
      | Tup(e1, e2) -> 
        let lst = gen_table e1 t1 and rst = gen_table e2 t2 in
        List.map lst ~f:(fun (lt, lx, le) ->
            List.map rst ~f:(fun (rt, rx, re) ->
                let and_x, s = gen_and lx le rx re in
                let and_cnf = gen_cnf and_x s in

                (`Tup(lt, rt), and_x, and_cnf)
              )
        ) |> List.concat
      | _ -> failwith "Unreachable")
    | TList(_) -> failwith "Not implemented"
    | _ -> failwith "Unreachable"
  in

  let tbl_cnfs = List.map (gen_table p.body t) ~f:(fun (label, _, c) ->
    (label, c))
  in

  {table=tbl_cnfs; weights=p.weights}


let compute_cnf ?debug (sharpsat_dir: String.t) (wcnf: LF.wcnf) : (LF.label * Bignum.t * Bignum.t) List.t = 
  let cnf_subf = Hashtbl.Poly.create () in

  let gen_output_cnf (c: LF.cnf) =
    let env = Hashtbl.Poly.create () in
    let temp_name, temp_outchannel = Filename.open_temp_file "dice" ".cnf" in

    let n = ref 0 in
    let fresh () =
      n := !n + 1;
      (Format.sprintf "%d" !n)
    in

    let cnf_string = Stdlib.Buffer.create 1000000 in
  
    let n_clauses = List.fold c ~init:0 ~f:(fun n d ->
      match d with
      | [] -> n
      | _ ->
        Stdlib.Buffer.add_char cnf_string '\n';
        List.iter d ~f:(fun l ->
          match l with
          | Pos(var) -> 
            let x = 
              match Hashtbl.Poly.find env var with
              | None -> 
                let x = fresh() in
                Hashtbl.Poly.add_exn env ~key:var ~data:x;
                x
              | Some(x) -> x 
            in
            Stdlib.Buffer.add_string cnf_string x;
            Stdlib.Buffer.add_char cnf_string ' ';
          | Neg(var) ->
            let x = 
              match Hashtbl.Poly.find env var with
              | None -> 
                let x = fresh() in
                Hashtbl.Poly.add_exn env ~key:var ~data:x;
                x
              | Some(x) -> x
            in
            Stdlib.Buffer.add_char cnf_string '-';
            Stdlib.Buffer.add_string cnf_string x;
            Stdlib.Buffer.add_char cnf_string ' ';);
        
        Stdlib.Buffer.add_char cnf_string '0';
        (n+1))
    in
  
    let n_vars = Hashtbl.Poly.fold env ~init:0 ~f:(fun ~key:var ~data:x n ->
      (match Hashtbl.Poly.find wcnf.weights var with
      | None -> ()
      | Some(f) -> 
        Stdlib.Buffer.add_string cnf_string "\nc p weight ";
        Stdlib.Buffer.add_string cnf_string x;
        Stdlib.Buffer.add_char cnf_string ' ';
        Stdlib.Buffer.add_string cnf_string (Bignum.to_string_accurate f);
        Stdlib.Buffer.add_string cnf_string " 0";);
      n+1)
    in
  
    let n_clauses_string = Format.sprintf "%d " n_clauses in
    let n_vars_string = Format.sprintf "%d " n_vars in

    let cnf_output = Stdlib.Buffer.create 1000000 in
    Stdlib.Buffer.add_string cnf_output "p cnf ";
    Stdlib.Buffer.add_string cnf_output n_vars_string;
    Stdlib.Buffer.add_string cnf_output n_clauses_string;
    Stdlib.Buffer.add_buffer cnf_output cnf_string;

    (* write to temp file *)
    protect ~f:(fun () -> Stdlib.Buffer.output_buffer temp_outchannel cnf_output) ~finally:(fun() ->Out_channel.close temp_outchannel);
    temp_name
  in

  let call_sharpsat (temp_name: String.t) : Bignum.t * Bignum.t = 
    let cwd = Unix.getcwd () in
    let cmd = "./sharpSAT" in
    let cmd = Format.sprintf "%s -WD -decot 30 -decow 100 -tmpdir . -cs 3500 %s" cmd temp_name in
    (match debug with
    | Some(true)->
      Format.printf "Call: %s\n" cmd;
    | _ -> ());

    (* call sharpSAT *)
    Unix.chdir sharpsat_dir;
    let inp = Unix.open_process_in cmd in
    let r = In_channel.input_lines inp in
    In_channel.close inp;
    Unix.chdir cwd;

    (* get result *)
    let p = match List.last r with
    | None -> failwith "Could not run sharpSAT"
    | Some(r) -> 
      let lst_line = String.split r ~on:' ' in
      let r = match List.last lst_line with
        | None -> failwith "Could not parse sharpSAT results"
        | Some(r) -> r
      in 
      r
    in

    let p = try Bignum.of_string p with
      _ -> failwith "sharpSAT did not solve within an hour"
    in

    (* get decisions *)
    let d = List.fold r ~init:"0" ~f:(fun acc line ->
      let lst_line = String.split line ~on:' ' in
      match lst_line with
      | ["c"; "o"; "decisions"; _] ->
        (match List.last lst_line with
        | None -> failwith "Could not parse sharpSAT results"
        | Some(r) -> String.strip r) 
      | _ -> acc
    )
    in

    let d = try Bignum.of_string d with
      _ -> failwith "sharpSAT did not solve within an hour"
    in

    p, d
  in

  List.map wcnf.table ~f:(fun (label, cnf_expr) -> 
    let cnf_t1 = Time.now() in
    let temp_name = gen_output_cnf cnf_expr in
    let cnf_t2 = Time.now() in
    let cnf_time = Time.diff cnf_t2 cnf_t1 in
    (match debug with
    | Some(true)->
      Format.printf "Gen CNF File Time: %s\n" (Time.Span.to_string cnf_time);
    | _ -> ());
    let prob, decisions = call_sharpsat temp_name in
    if Bignum.(prob = zero) then (label, Bignum.zero, decisions) else
      (label, prob, decisions))


let get_prob p =
  let c = compile_program ~eager_eval:false p in
  let z = Wmc.wmc ~float_wmc:false c.ctx.man c.body.z c.ctx.weights in
  let prob = Wmc.wmc ~float_wmc:false c.ctx.man (Bdd.bdd_and c.ctx.man (extract_leaf c.body.state) c.body.z) c.ctx.weights in
  (* Format.printf "prob: %f, z: %f" prob z; *)
  Bignum.(prob / z)


module I = Parser.MenhirInterpreter
open Lexing
open Lexer


exception Syntax_error of string


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)



(** [parse_and_prob] parses and computes the probability for string [txt] *)
let parse_and_prob ?debug txt =
  let buf = Lexing.from_string txt in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith (Format.sprintf "Error parsing %s" txt)
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith (Format.sprintf "Error parsing %s" txt) in
  let (_, transformed) = Passes.from_external_prog false (Passes.expand_recursion parsed) in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
     Format.printf "After passes: %s\n" (CoreGrammar.string_of_prog (transformed));
   | _ -> ());
   Bignum.to_float (get_prob transformed)

let parse_optimize_and_prob ?debug txt =
  let buf = Lexing.from_string txt in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith (Format.sprintf "Error parsing %s" txt)
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith (Format.sprintf "Error parsing %s" txt) in
  let (_, transformed) = Passes.from_external_prog_optimize false (Passes.expand_recursion parsed) true true None true true in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
     Format.printf "After passes: %s\n" (CoreGrammar.string_of_prog (transformed));
   | _ -> ());
   Bignum.to_float (get_prob transformed)

let get_lexing_position lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)


let get_parse_error env =
    match I.stack env with
    | lazy Nil -> "Invalid syntax"
    | lazy (Cons (I.Element (state, _, _, _), _)) ->
        try (Parser_messages.message (I.number state)) with
        | _ -> "invalid syntax (no specific message for this eror)"


(** [parse_with_error] parses [lexbuf] as a program or fails with a syntax error *)
let parse_with_error lexbuf =
  let rec helper lexbuf checkpoint =
    match checkpoint with
    | I.InputNeeded _env ->
      (* The parser needs a token. Request one from the lexer,
         and offer it to the parser, which will produce a new
         checkpoint. Then, repeat. *)
      let token = Lexer.token lexbuf in
      let startp = lexbuf.lex_start_p
      and endp = lexbuf.lex_curr_p in
      let checkpoint = I.offer checkpoint (token, startp, endp) in
      helper lexbuf checkpoint
    | I.Shifting _
    | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      helper lexbuf checkpoint
    | I.HandlingError _env ->
      (* The parser has suspended itself because of a syntax error. Stop. *)
      let line, pos = get_lexing_position lexbuf in
      let err = get_parse_error _env in
      raise (Syntax_error (Format.sprintf "Error at line %d, position %d: %s\n%!" line pos err))
    | I.Accepted v -> v
    | I.Rejected ->
      (* The parser rejects this input. This cannot happen, here, because
         we stop as soon as the parser reports [HandlingError]. *)
      assert false in
  helper lexbuf (Parser.Incremental.program lexbuf.lex_curr_p)

