(** The core compilation engine for Dice *)

open Core
open Cudd
open Wmc
open VarState
module CG = CoreGrammar
module VO = VarOrder


type subst = (Bdd.dt * Bdd.dt) List.t

(** Result of compiling an expression *)
type compiled_expr = {
  state: Bdd.dt btree;
  z: Bdd.dt;
  subst: subst;
  flips: Bdd.dt List.t;
}

type compiled_func = {
  args: (Bdd.dt btree) List.t;
  body: compiled_expr;

  local_bools: int List.t;
  arg_bools: int List.t;
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

type env = (String.t, Bdd.dt btree) Map.Poly.t (* map from variable identifiers to BDDs*)


let new_context count =
  let man = Man.make_d ~numVars:count () in
  (* Man.enable_autodyn man Man.REORDER_LINEAR; *)
  Man.disable_autodyn man;
  let weights = Hashtbl.Poly.create () in
  let names = Hashtbl.Poly.create () in
  {man = man;
   name_map = names;
   weights = weights;
   funcs = Hashtbl.Poly.create ();}

(** generates a symbolic representation for a variable of the given type *)
(* let rec gen_sym_type ctx (t:CG.typ) : Bdd.dt btree =
  match t with
  | TBool ->
    let bdd = Bdd.newvar ctx in Leaf(bdd)
  | TTuple(t1, t2) ->
    let s1 = gen_sym_type ctx t1 and s2 = gen_sym_type ctx t2 in
    Node(s1, s2) *)

let rec is_const (st: Bdd.dt btree) =
  match st with
  | Leaf(v) -> Bdd.is_cst v
  | Node(l, r) -> (is_const l) && (is_const r)

type state = Bdd.dt btree

let rec compile_expr (ctx: compile_context) (tenv: CG.tenv)
    (env: env) (subst: subst) (z: Bdd.dt) (e: VO.texpr) : compiled_expr =
  let binop_helper f e1 e2 =
    let c1 = compile_expr ctx tenv env subst z e1 in
    let c2 = compile_expr ctx tenv env c1.subst c1.z e2 in
    let v = Leaf(f (extract_leaf c1.state) (extract_leaf c2.state)) in
    let z = Bdd.dand c1.z c2.z in
    {state=v; z=z; subst=c2.subst; flips=List.append c1.flips c2.flips} in

  let r = match e with
  | And(e1, e2) -> binop_helper Bdd.dand e1 e2
  | Or(e1, e2) -> binop_helper Bdd.dor e1 e2
  | Xor(e1, e2) -> binop_helper Bdd.xor e1 e2
  | Eq(e1, e2) -> binop_helper Bdd.eq e1 e2
  | Not(e) ->
    let c = compile_expr ctx tenv env subst z e in
    let v = Bdd.dnot (extract_leaf c.state) in
    {state=Leaf(v); subst=c.subst; z=c.z; flips=c.flips}

  | True -> {state=Leaf(Bdd.dtrue ctx.man); subst=subst; z=Bdd.dtrue ctx.man; flips=[]}

  | False -> {state=Leaf(Bdd.dfalse ctx.man); subst=subst; z=Bdd.dtrue ctx.man; flips=[]}

  | Ident(s) ->
    (match Map.Poly.find env s with
     | Some(r) -> {state=r; z=Bdd.dtrue ctx.man; flips=[]; subst=subst}
     | _ -> failwith (sprintf "Could not find variable '%s'" s))

  | Tup(e1, e2) ->
    let c1 = compile_expr ctx tenv env subst z e1 in
    let c2 = compile_expr ctx tenv env c1.subst c1.z e2 in
    {state=Node(c1.state, c2.state); z=c2.z; subst=c2.subst; flips=List.append c1.flips c2.flips}

  | Ite(g, thn, els) ->
    let cg = compile_expr ctx tenv env subst z g in
    if is_const cg.state then
      let v = extract_leaf cg.state in
      let r = compile_expr ctx tenv env cg.subst cg.z (if Bdd.is_true v then thn else els) in
      {state=r.state; z=Bdd.dand cg.z r.z; subst=r.subst; flips = cg.flips @ r.flips}
    else
      let cthn = compile_expr ctx tenv env cg.subst cg.z thn in
      let cels = compile_expr ctx tenv env cthn.subst cthn.z els in
      let gbdd = extract_leaf cg.state in
      let zipped = zip_tree cthn.state cels.state in
      let v' = map_tree zipped (fun (thn_state, els_state) ->
          Bdd.ite gbdd thn_state els_state
        ) in
      let z' = Bdd.dand cg.z (Bdd.ite gbdd cthn.z cels.z) in
      {state=v'; z=z'; flips = List.append cg.flips (List.append cthn.flips cels.flips); subst=cels.subst}

  | Fst(e) ->
    let c = compile_expr ctx tenv env subst z e in
    let v' = (match c.state with
     | Node(l, _) -> l
     | _ -> failwith (Format.sprintf "Internal Failure: calling `fst` on non-tuple at %s" (VO.string_of_texpr e))) in
    {state=v'; z=c.z; flips=c.flips; subst=c.subst}

  | Snd(e) ->
    let c = compile_expr ctx tenv env subst z e in
    let v' = (match c.state with
     | Node(_, r) -> r
     | _ -> failwith (Format.sprintf "Internal Failure: calling `snd` on non-tuple at %s" (VO.string_of_texpr e))) in
    {state=v'; z=c.z; flips=c.flips; subst=c.subst}

  | Flip(f, idx) ->
    let new_f = Bdd.ithvar ctx.man idx in
    let var_lbl = Bdd.topvar new_f in
    let var_name = (Format.sprintf "f%d" idx) in
    Hashtbl.Poly.add_exn ctx.weights ~key:var_lbl ~data:(1.0-.f, f);
    Hashtbl.add_exn ctx.name_map ~key:var_lbl ~data:var_name;
    {state=Leaf(new_f); z=Bdd.dtrue ctx.man; flips=[new_f]; subst=subst}

  | Observe(g) ->
    let c = compile_expr ctx tenv env subst z g in
    {state=Leaf(Bdd.dtrue ctx.man); z=Bdd.dand (extract_leaf c.state) c.z; flips=c.flips; subst=c.subst}

  | Let(x, e1, e2, tree) ->
    let c1 = compile_expr ctx tenv env subst z e1 in
    let t = (VO.type_of tenv e1) in
    let tenv' = Map.Poly.set tenv ~key:x ~data:t in
    if is_const c1.state then (* this value is a heuristic *)
      let env' = Map.Poly.set env ~key:x ~data:c1.state in
      let c2 = compile_expr ctx tenv' env' c1.subst c1.z e2 in
      {state=c2.state; z=Bdd.dand c1.z c2.z; flips=List.append c1.flips c2.flips; subst=c2.subst}
    else
      (* create a temp variable *)
      let tmp = VarState.map_tree tree (fun idx -> Bdd.ithvar ctx.man idx) in
      let env' = Map.Poly.set env ~key:x ~data:tmp in
      let newsubst = List.zip_exn (collect_leaves tmp) (collect_leaves c1.state) in
      let c2 = compile_expr ctx tenv' env' (newsubst @ subst) c1.z e2 in
      (* do substitution *)
      let swap_idx = List.to_array (List.map (collect_leaves tmp) ~f:(Bdd.topvar)) in
      let swap_bdd = List.to_array (collect_leaves c1.state) in
      let final_state = map_tree c2.state (fun bdd ->
          List.fold ~init:bdd newsubst ~f:(fun acc (tmp, e1c) ->
              Bdd.compose (Bdd.topvar tmp) e1c acc
            )
        ) in
      let final_z = Bdd.labeled_vector_compose c2.z swap_bdd swap_idx in
      {state=final_state; z=Bdd.dand c1.z final_z; flips=List.append c1.flips c2.flips; subst = c2.subst}

  | Sample(e) ->
    let c = compile_expr ctx tenv env subst z e in
    (* substitute *)
    let comp = List.fold ~init:c.state c.subst ~f:(fun acc (arg, subst) ->
        VarState.map_tree acc (fun treebdd -> Bdd.compose (Bdd.topvar arg) subst treebdd)
      ) in
    let z' = List.fold ~init:(Bdd.dand z c.z) c.subst ~f:(fun acc (arg, subst) ->
        Bdd.compose (Bdd.topvar arg) subst acc
      ) in
    let rec sequential_sample cur_obs state =
      (match state with
       | Leaf(bdd) ->
         let t = Wmc.wmc (Bdd.dand (Bdd.dand cur_obs bdd) z') ctx.weights in
         let curz = Wmc.wmc (Bdd.dand z' cur_obs) ctx.weights in
         let rndvalue = Random.float 1.0 in
         Format.printf "z: %f, v: %f, accepted: %s\n" curz t
           (if compare_float rndvalue (t /. curz) < 0 then "yes" else "no");
         if compare_float rndvalue (t /. curz) < 0 then (bdd, Leaf(Bdd.dtrue ctx.man)) else (Bdd.dnot bdd, Leaf(Bdd.dfalse ctx.man))
       | Node(l, r) ->
         let lbdd, lres = sequential_sample cur_obs l in
         let rbdd, rres = sequential_sample lbdd r in
         (rbdd, Node(lres, rres))
      ) in
    let _, r = sequential_sample (Bdd.dtrue ctx.man) comp in
    let obs = List.fold ~init:(Bdd.dtrue ctx.man) (List.zip_exn (collect_leaves comp) (collect_leaves r))
        ~f:(fun acc (st, obs) ->
            if Bdd.is_true obs then Bdd.dand acc st
            else if Bdd.is_false obs then Bdd.dand acc (Bdd.dnot st)
            else failwith "unreachable"
          ) in
    {state=r; z=Bdd.dand obs z; subst = subst; flips=[]}
    (* {state=r; z=z; subst = subst; flips=[]} *)

  | FuncCall(name, args, order_map) ->
    let func = try Hashtbl.Poly.find_exn ctx.funcs name
      with _ -> failwith (Format.sprintf "Could not find function '%s'." name) in

    let curz = ref z in
    let cursubst = ref subst in
    let cargs = List.map args ~f:(fun i ->
        let r = compile_expr ctx tenv env !cursubst !curz i in
        curz := r.z;
        cursubst := r.subst;
        r) in
    let argflips = List.fold cargs ~init:[] ~f:(fun acc i -> acc @ i.flips) in
    let new_flips = List.map func.body.flips ~f:(fun v -> Bdd.ithvar ctx.man (Map.Poly.find_exn order_map (Bdd.topvar v))) in
    (* let swapA = List.to_array (List.map new_flips ~f:(fun cur -> Bdd.topvar cur)) in
    let swapB = List.to_array (List.map func.body.flips ~f:(fun cur -> Bdd.topvar cur)) in
    let refreshed_state = map_tree func.body.state (fun bdd -> Bdd.swapvariables bdd swapA swapB) in
    let refreshed_z = Bdd.swapvariables func.body.z swapA swapB in
    let swap_idx =
      List.map func.args ~f:(fun arg ->
          List.to_array (List.map (collect_leaves arg) ~f:(Bdd.topvar)))
      |> Array.concat in
    let swap_bdd =
      List.map cargs ~f:(fun arg ->
          List.to_array (collect_leaves arg.state))
      |> Array.concat in
    let final_state = map_tree refreshed_state (fun bdd ->
        Bdd.labeled_vector_compose bdd swap_bdd swap_idx) in
    let final_z = Bdd.labeled_vector_compose refreshed_z swap_bdd swap_idx in *)
    let order_pairs = Map.Poly.to_alist order_map in
    (* print_endline "state = <<";
    BddUtil.dump_dot (Hashtbl.Poly.create ()) (extract_leaf func.body.state);
    print_endline "\n>>"; *)
    (* print_endline ""; *)
    (* Map.Poly.sexp_of_t sexp_of_int sexp_of_int order_map |> Sexp.to_string_hum |> print_endline; *)
    (* [%sexp_of: (int, float*float) Hashtbl.Poly.t] ctx.weights |> Sexp.to_string_hum |> print_endline; *)
    List.iter order_pairs (fun (old_id, new_id) ->
      let wts_option = Hashtbl.Poly.find ctx.weights old_id in
      match wts_option with
      | Some wts -> Hashtbl.Poly.add_exn ctx.weights ~key:new_id ~data: wts
      | None -> ()
      (* let wts = Hashtbl.Poly.find_exn ctx.weights old_id in
      Hashtbl.Poly.add_exn ctx.weights ~key:new_id ~data: wts *)
    ) ;
    let old_ids = List.map order_pairs (fun (x,y) -> x) |> List.to_array in
    (* let new_ids = List.map order_pairs (fun (x,y) -> y) |> List.to_array in *)
    (* let (arg_start, arg_end) = arg_range in *)
    let (arg_start, arg_end) =
      if (List.length func.arg_bools) > 0 then
        (List.nth_exn func.arg_bools 0, List.last_exn func.arg_bools)
      else
        (0, -1)
      in
    let arg_leaves = List.map cargs ~f:(fun carg ->
          List.to_array (collect_leaves carg.state))
      |> Array.concat in
    let new_bdds = List.map order_pairs (fun (x,y) ->
      if x >= arg_start && x <= arg_end then Array.get arg_leaves (x - arg_start)
      else 
      Bdd.ithvar ctx.man y
    ) |> List.to_array in
    let final_state = map_tree func.body.state (fun bdd ->
        Bdd.labeled_vector_compose bdd new_bdds old_ids
      ) in
(*     print_endline "final state = <<";
    BddUtil.dump_dot (Hashtbl.Poly.create ()) (extract_leaf final_state);
    print_endline "\n>>"; *)
    let final_z = Bdd.labeled_vector_compose func.body.z new_bdds old_ids in
    {state=final_state; z=Bdd.dand !curz final_z; flips=new_flips @ argflips; subst= !cursubst}
  in r

let compile_func (ctx: compile_context) tenv (f: VO.func) : compiled_func =
  (* set up the context; need both a list and a map, so build both together *)
  let new_tenv = List.fold ~init:tenv f.args ~f:(fun acc (name, typ) ->
      Map.Poly.add_exn acc ~key:name ~data:typ
    ) in
  let count = ref 0 in
  let (args, env) = List.fold f.args ~init:([], Map.Poly.empty)
      ~f:(fun (lst, map) (name, typ) ->
          let iarg = VO.mk_tree count typ in
          let placeholder_arg = map_tree iarg (fun i ->
            let i' = List.nth_exn f.arg_bools i in
            Bdd.ithvar ctx.man i'
          ) in
          (List.append lst [placeholder_arg], Map.Poly.set map ~key:name ~data:placeholder_arg)
        ) in
  (* now compile the function body with these arguments *)
  let body = compile_expr ctx new_tenv env [] (Bdd.dtrue ctx.man) f.body in
  {args = args; body = body; arg_bools = f.arg_bools; local_bools = f.local_bools}

let compile_program (p:CG.program) : compiled_program =
  (* first compile the functions in topological order *)
  let (count, vp) = VO.from_cg_prog VO.DFS p in
  let ctx = new_context count in
  let tenv = ref Map.Poly.empty in
  List.iter p.functions ~f:(fun cg_func ->
      let func = Map.Poly.find_exn vp.functions cg_func.name in
      let c = compile_func ctx !tenv func in
      tenv := Map.Poly.add_exn !tenv ~key:func.name ~data:(VO.type_of_fun !tenv func);
      try Hashtbl.Poly.add_exn ctx.funcs ~key:func.name ~data:c
      with _ -> failwith (Format.sprintf "Function names must be unique: %s found twice" func.name)
    );
  (* now compile the main body, which is the result of the program *)
  let env = Map.Poly.empty in
  let c = compile_expr ctx !tenv env [] (Bdd.dtrue ctx.man) vp.body in
  (* do substitutions *)
  let subst = List.fold ~init:c.state c.subst ~f:(fun acc (arg, subst) ->
      VarState.map_tree acc (fun treebdd -> Bdd.compose (Bdd.topvar arg) subst treebdd)
    ) in
  let z' = List.fold ~init:c.z c.subst ~f:(fun acc (arg, subst) ->
      Bdd.compose (Bdd.topvar arg) subst acc
    ) in
  {ctx = ctx; body = {state = subst; z = z'; flips=c.flips; subst=[]}}


let get_prob p =
  let c = compile_program p in
  let z = Wmc.wmc c.body.z c.ctx.weights in
  let prob = Wmc.wmc (Bdd.dand (extract_leaf c.body.state) c.body.z) c.ctx.weights in
  prob /. z


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
  let (_, transformed) = Passes.from_external_prog parsed in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
     Format.printf "After passes: %s\n" (CoreGrammar.string_of_prog (transformed));
   | _ -> ());
  get_prob transformed

let parse_optimize_and_prob ?debug txt =
  let buf = Lexing.from_string txt in
  let parsed = try Parser.program Lexer.token buf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position buf msg;
    failwith (Format.sprintf "Error parsing %s" txt)
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position buf;
    failwith (Format.sprintf "Error parsing %s" txt) in
  let (_, transformed) = Passes.from_external_prog_optimize parsed in
  (match debug with
   | Some(true)->
     Format.printf "Program: %s\n" (ExternalGrammar.string_of_prog parsed);
     Format.printf "After passes: %s\n" (CoreGrammar.string_of_prog (transformed));
   | _ -> ());
  get_prob transformed

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

