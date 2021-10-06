open Core
open Wmc
open VarState
open CoreGrammar
open Bdd

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
let rec gen_sym_type ctx (t:typ) : bddptr btree =
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

let rec compile_expr (ctx: compile_context) (tenv: tenv) (env: env) e : compiled_expr =
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
     | _ -> failwith (Format.sprintf "Internal Failure: calling `fst` on non-tuple at %s" (string_of_expr e))) in
    {state=v'; z=c.z; flips=c.flips}

  | Snd(e) ->
    let c = compile_expr ctx tenv env e in
    let v' = (match c.state with
     | Node(_, r) -> r
     | _ -> failwith (Format.sprintf "Internal Failure: calling `snd` on non-tuple at %s" (string_of_expr e))) in
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
    let t = (type_of tenv e1) in
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

let compile_func (ctx: compile_context) tenv (f: func) : compiled_func =
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

let compile_program (p:program) ~eager_eval : compiled_program =
  (* first compile the functions in topological order *)
  let ctx = new_context ~eager_eval () in
  let tenv = ref Map.Poly.empty in
  List.iter p.functions ~f:(fun func ->
      let c = compile_func ctx !tenv func in
      tenv := Map.Poly.add_exn !tenv ~key:func.name ~data:(type_of_fun !tenv func);
      try Hashtbl.Poly.add_exn ctx.funcs ~key:func.name ~data:c
      with _ -> failwith (Format.sprintf "Function names must be unique: %s found twice" func.name)
    );
  (* now compile the main body, which is the result of the program *)
  let env = Map.Poly.empty in
  {ctx = ctx; body = compile_expr ctx !tenv env p.body}


let get_prob p =
  let c = compile_program ~eager_eval:false p in
  let z = Wmc.wmc ~wmc_type:0 c.ctx.man c.body.z c.ctx.weights in
  let prob = Wmc.wmc ~wmc_type:0 c.ctx.man (Bdd.bdd_and c.ctx.man (extract_leaf c.body.state) c.body.z) c.ctx.weights in
  (* Format.printf "prob: %f, z: %f" prob z; *)
  LogProbability.rat_div_and_conv prob z


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
  let (_, transformed) = Passes.from_external_prog (Passes.expand_recursion parsed) in
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
  let (_, transformed) = Passes.from_external_prog_optimize (Passes.expand_recursion parsed) true true true in
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

