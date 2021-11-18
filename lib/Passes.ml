(** Performs optimization passes over the core grammar **)
open Core
open Util
module EG = ExternalGrammar
module CG = CoreGrammar

type config = { max_list_length: int }

let default_recursion_limit = 10

let default_config = { max_list_length = default_recursion_limit }

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let within_epsilon x y =
  (Float.compare (Float.abs (x -. y)) 0.0001) < 0

let map_eexpr f =
  let open EG in
  function
  | And(s, e1, e2) -> And(s, f e1, f e2)
  | Or(s, e1, e2) -> Or(s, f e1, f e2)
  | Iff(s, e1, e2) -> Iff(s, f e1, f e2)
  | Xor(s, e1, e2) -> Xor(s, f e1, f e2)
  | Sample(s, e) -> Sample(s, f e)
  | IntConst(s, i) -> IntConst(s, i)
  | Not(s, e) -> Not(s, f e)
  | Ite(s, e1, e2, e3) -> Ite(s, f e1, f e2, f e3)
  | Flip(s, p) -> Flip(s, p)
  | Let(s, id, e1, e2) -> Let(s, id, f e1, f e2)
  | Observe(s, e) -> Observe(s, f e)
  | Ident(s, id) -> Ident(s, id)
  | Discrete(s, ps) -> Discrete(s, ps)
  | Int(s, sz, v) -> Int(s, sz, v)
  | Eq(s, e1, e2) -> Eq(s, f e1, f e2)
  | LeftShift(s, e, i) -> LeftShift(s, f e, i)
  | RightShift(s, e, i) -> RightShift(s, f e, i)
  | Plus(s, e1, e2) -> Plus(s, f e1, f e2)
  | Minus(s, e1, e2) -> Minus(s, f e1, f e2)
  | Mult(s, e1, e2) -> Mult(s, f e1, f e2)
  | Div(s, e1, e2) -> Div(s, f e1, f e2)
  | Lte(s, e1, e2) -> Lte(s, f e1, f e2)
  | Lt(s, e1, e2) -> Lt(s, f e1, f e2)
  | Gte(s, e1, e2) -> Gte(s, f e1, f e2)
  | Gt(s, e1, e2) -> Gt(s, f e1, f e2)
  | Neq(s, e1, e2) -> Neq(s, f e1, f e2)
  | Fst(s, e) -> Fst(s, f e)
  | Snd(s, e) -> Snd(s, f e)
  | Tup(s, e1, e2) -> Tup(s, f e1, f e2)
  | FuncCall(s, fn, es) -> FuncCall(s, fn, List.map es ~f)
  | Iter(s, fn, e, n) -> Iter(s, fn, f e, n)
  | Unif(s, sz, b, e) -> Unif(s, sz, b, e) 
  | Binom(s, sz, n, p) -> Binom(s, sz, n, p)
  | True s -> True s
  | False s -> False s
  | ListLit(s, es) -> ListLit(s, List.map es ~f)
  | ListLitEmpty(s, t) -> ListLitEmpty(s, t)
  | Cons(s, e1, e2) -> Cons(s, f e1, f e2)
  | Head(s, e) -> Head(s, f e)
  | Tail(s, e) -> Tail(s, f e)
  | Length(s, e) -> Length(s, f e)

let unreachable e =
  let open EG in
  Let(gen_src, "$_", Observe(gen_src, False gen_src), e)

let rec gen_default_value =
  let open EG in
  function
  | TBool -> False gen_src
  | TInt sz -> Int(gen_src, sz, 0)
  | TTuple(t1, t2) -> Tup(gen_src, gen_default_value t1, gen_default_value t2)
  | TList t -> ListLitEmpty(gen_src, TList t)
  | TFunc _ -> failwith "Internal Error: gen_default_value called with function type"

let expand_recursion ?(recursion_limit = default_recursion_limit) (p: EG.program) =
  let open EG in
  let expand_func func =
    let gen_name i = Format.sprintf "%s$%d" func.name i in
    let is_recursive = ref false in
    let rec sub i e = map_eexpr (sub i) @@ match e with
      | FuncCall(s, fn, es) when String.(fn = func.name) ->
        is_recursive := true;
        FuncCall(s, gen_name i, es)
      | _ -> e in
    let body' = sub 0 func.body in
    if !is_recursive then
      match func.return_type with
      | Some rt ->
        let base_copy =
          { func with name = gen_name recursion_limit
          ; body = unreachable (gen_default_value rt) } in
        let rec_copies = List.map (List.range 0 recursion_limit)
          ~f:(fun i -> { func with name = gen_name i
                       ; body = sub (succ i) func.body }) in
        base_copy :: List.rev_append rec_copies [{ func with body = body' }]
      | None -> raise @@ Type_error (Format.sprintf
        "Type error in function %s: \
          return type annotation is required for recursive functions"
        func.name)
    else [func] in
  { p with functions = List.concat_map p.functions ~f:expand_func }

let rec expand_iter s f curv k : EG.eexpr =
  assert (k >= 0);
  if k = 0 then curv else
    Let(s, "$iterident", FuncCall(s, f, [curv]), expand_iter s f (Ident(s, "$iterident")) (k-1))

let inline_functions (p: EG.program) =
  let open EG in
  let function_map = List.fold p.functions ~init:(Map.Poly.empty) ~f:(fun acc f ->
      Map.Poly.add_exn acc ~key:f.name ~data:f) in
  let rec helper (e: EG.eexpr) =
    match e with
    | Iff(s, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in Eq(s, s1, s2)
    | Lte(s, e1, e2) -> helper(Or(s, Lt(s, e1, e2), Eq(s, e1, e2)))
    | Gt(s, e1, e2) -> helper(Not(s, Lte(s, e1, e2)))
    | Gte(s, e1, e2) -> helper(Not(s, Lt(s, e1, e2)))
    | Iter(s, f, init, k) -> helper (expand_iter s f init k)
    | FuncCall(s, "nth_bit", args) ->
      FuncCall(s, "nth_bit", List.map args ~f:helper)
    | FuncCall(s, id, args) ->
      let cur_f = try Map.Poly.find_exn function_map id
        with _ -> failwith (Format.sprintf "Internal error: could not find inlined function %s" id) in
      let inlined = helper cur_f.body in
      List.fold (List.zip_exn cur_f.args args) ~init:inlined ~f:(fun acc (arg, v) -> Let(s, fst arg, v, acc))
    | _ -> map_eexpr helper e in
  {functions=[]; body=helper p.body}

let num_paths (p: EG.program) : LogProbability.t =
  let inlined = inline_functions p in
  let rec helper (e: EG.eexpr) =
    match e with
    | And(_,e1, e2)
    | Or(_,e1, e2)
    | Plus(_,e1, e2)
    | Eq(_,e1, e2)
    | Minus(_,e1, e2)
    | Neq(_,e1, e2)
    | Div(_,e1, e2)
    | Mult(_,e1, e2)
    | Lt(_,e1, e2)
    | Gt(_,e1, e2)
    | Lte(_,e1, e2)
    | Gte(_,e1, e2)
    | Tup(_,e1, e2)
    | Let(_,_, e1, e2)
    | Cons(_, e1, e2) ->
      let s1 = helper e1 in
      let s2 = helper e2 in LogProbability.mult s1 s2
    | Not(_,e) -> helper e
    | Flip(_,_) -> LogProbability.make 2.0
    | Ident(_,_) | Int(_,_, _) | True(_) | False(_) | ListLitEmpty(_, _) ->
      LogProbability.make 1.0
    | Discrete(_,l) -> LogProbability.make (float_of_int (List.length l))
    | Unif(_, _, b, e) -> LogProbability.make (float_of_int (e-b))
    | Binom(_, _, n, p) -> LogProbability.make (float_of_int (n+1))
    | Observe(_,e) -> helper e
    | Ite(_,g, thn, els) ->
      let gc = helper g in
      let tc = helper thn in
      let ec = helper els in
      LogProbability.mult gc (LogProbability.add tc ec)
    | Snd(_,e) | Fst(_, e)
    | Head(_, e) | Tail(_, e) | Length(_, e) -> helper e
    | ListLit(_, es) -> List.reduce_exn (List.map es ~f:helper) ~f:LogProbability.mult
    | _ -> failwith "unreachable, functions inlined" in
  helper inlined.body

let num_binary_digits d = int_of_float (floor (Util.log2 (float_of_int (d)))) + 1

(** converts a little-endian binary vector into an integer *)
let bin_to_int l =
  let sz = (List.length l) - 1 in
  List.foldi l ~init:0 ~f:(fun idx acc i -> acc + (i lsl (sz - idx)))

(** converts a little-endian binary vector into an integer *)
let int_to_bin final_sz d =
  let rec helper cur_pos d =
    if cur_pos >= 0 then
      let cur_v = 1 lsl cur_pos in
      let p' = cur_pos - 1 in
      if d < cur_v then [0] @ (helper p' d) else [1] @ (helper p' (d - cur_v))
    else [] in
  let sz = (num_binary_digits d) - 1 in
  let r = helper sz d in
  let padding = List.init (final_sz - List.length r) ~f:(fun _ -> 0) in
  padding @ r

(** builds a list of all assignments to `l`, a list of (expr, bdd) *)
let rec all_assignments mgr l =
  let open Cudd in
  let open CG in
  match l with
  | [] -> [True, Bdd.dtrue mgr]
  | (cur_constraint, cur_bdd)::xs ->
    let l1 = List.map (all_assignments mgr xs)
        ~f:(fun (constr, bdd) -> And(cur_constraint, constr), Bdd.dand cur_bdd bdd) in
    let l2 = List.map (all_assignments mgr xs)
        ~f:(fun (constr, bdd) -> And(Not(cur_constraint), constr), Bdd.dand (Bdd.dnot cur_bdd) bdd) in
    l1 @ l2

let fold_with_seen l ~init ~f =
  let (_, r) = List.fold l ~init:(([], init)) ~f:(fun (seen, acc) i ->
      let r = f seen acc i in
      ([i] @ seen, r)) in
  r

(* given a list of expressions [e1; e2; e3; ..] makes a
   tuple that looks like (e1, (e2, (e3, ...)))*)
let rec mk_dfs_tuple l =
  match l with
  | [] -> failwith "cannot call with empty list"
  | [x] -> x
  | x::xs ->
    CG.Tup(x, mk_dfs_tuple xs)

let rec type_eq t1 t2 =
  let open EG in
  match (t1, t2) with
  | (TBool, TBool) -> true
  | ((TTuple(ll, lr), TTuple(rl, rr))) ->
    (type_eq ll rl) && (type_eq lr rr)
  | (TInt(d1), TInt(d2)) when d1 = d2 -> true
  | TList l, TList r -> type_eq l r
  | _ -> false

type source = EG.source
[@@deriving sexp_of]

type ast =
    And of source * tast * tast
  | LeftShift of source * tast * int
  | RightShift of source * tast * int
  | Sample of source * tast
  | Or of source * tast * tast
  | Iff of source * tast * tast
  | Xor of source * tast * tast
  | IntConst of source * int
  | Not of source * tast
  | Ite of source * tast * tast * tast
  | Flip of source * Bignum.t
  | Let of source * String.t * tast * tast
  | Observe of source * tast
  | Ident of source * String.t
  | Discrete of source * Bignum.t List.t
  | Int of source * int * int (* value, size *)
  | Eq of source * tast * tast
  | Plus of source * tast * tast
  | Minus of source * tast * tast
  | Mult of source * tast * tast
  | Div of source * tast * tast
  | Lte of source * tast * tast
  | Lt of source * tast * tast
  | Gte of source * tast * tast
  | Gt of source * tast * tast
  | Neq of source * tast * tast
  | Fst of source * tast
  | Snd of source * tast
  | Tup of source * tast * tast
  | FuncCall of source * String.t * tast List.t
  | Iter of source * String.t * tast * int
  | Unif of source * int * int * int
  | Binom of source * int * int * Bignum.t
  | True of source
  | False of source
  | ListLit of source * tast List.t
  | ListLitEmpty of source
  | Cons of source * tast * tast
  | Head of source * tast
  | Tail of source * tast
  | Length of source * tast
and
  tast = EG.typ * ast
[@@deriving sexp_of]

let string_of_tast (a: tast) =
  Sexp.to_string_hum (sexp_of_tast a)

type arg = EG.arg
[@@deriving sexp_of]

type func = { name: String.t; args: arg List.t; body: tast}
[@@deriving sexp_of]

type program = { functions: func List.t; body: tast }
[@@deriving sexp_of]

type typ_ctx = { in_func: bool }

let get_col (pos: EG.lexing_position) =
  pos.pos_cnum - pos.pos_bol

let rec type_of (cfg: config) (ctx: typ_ctx) (env: EG.tenv) (e: EG.eexpr) : tast =
  let open EG in
  let expect_t e (src: EG.lexing_position) typ : tast =
    let (t, e) = type_of cfg ctx env e in
    if (type_eq t typ) then (t, e) else
      raise (EG.Type_error(Format.sprintf "Type error at line %d column %d: expected %s, got %s"
                                      src.pos_lnum (get_col src) (EG.string_of_typ typ) (EG.string_of_typ t))) in
  let expect_t' typ e = expect_t e (get_src e).startpos typ in
  let expect_compatible_int (f: tast -> tast -> ast) src e1 e2 lbl =
    let (t1, s1) = type_of cfg ctx env e1 and (t2, s2) = type_of cfg ctx env e2 in
    match (t1, t2) with
    | (TInt(d1), TInt(d2)) when d1 = d2 -> (d1, f (t1, s1) (t1, s2))
    | (_, _) ->
      raise (EG.Type_error(Format.sprintf "Type error at line %d column %d: expected compatible integer types for operation '%s', got %s and %s"
                             src.pos_lnum (get_col src) lbl (EG.string_of_typ t1) (EG.string_of_typ t2)))  in
  let expect_list e : typ * tast =
    let (t, e') = type_of cfg ctx env e in
    match t with
    | TList t' -> (t', (t, e'))
    | _ ->
      let pos = (get_src e).startpos in
      raise (Type_error (Format.sprintf "Type error at line %d column %d: expected a list type, got %s"
                          pos.pos_lnum (get_col pos) (string_of_typ t))) in
  match e with
  | And(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, And(s, s1, s2))
  | Or(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, Or(s, s1, s2))
  | Iff(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, Iff(s, s1, s2))
  | Sample(s, e1) ->
    if ctx.in_func then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: \
                                         Sampling within functions is not permitted"
                           s.startpos.pos_lnum (get_col s.startpos)));
    let t, e = type_of cfg ctx (Map.Poly.empty) e1 in
    (t, Sample(s, (t, e)))
  | Xor(s, e1, e2) ->
    let s1 = expect_t e1 s.startpos TBool in
    let s2 = expect_t e2 s.startpos TBool in
    (TBool, Xor(s, s1, s2))
  | Not(s, e1) ->
    let s1 = expect_t e1 s.startpos TBool in
    (TBool, Not(s, s1))
  | Observe(s, e1) ->
    let s1 = expect_t e1 s.startpos TBool in
    (TBool, Observe(s, s1))
  | True(s) -> (TBool, True(s))
  | False(s) -> (TBool, False(s))
  | Flip(s, f) -> (TBool, Flip(s, f))
  | Ident(src, s) ->
    let t = (try Map.Poly.find_exn env s
     with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: \
                                         Could not find variable '%s' during typechecking"
                                    src.startpos.pos_lnum (get_col src.startpos) s))) in
    (t, Ident(src, s))
  | Fst(s, e1) ->
    let (t, s1) = type_of cfg ctx env e1 in
    let t' = (match t with
     | TTuple(l, _) -> l
     | t -> raise (Type_error (Format.sprintf "Type error at line %d column %d: expected tuple, got %s"
                                 s.startpos.pos_lnum (get_col s.startpos) (string_of_typ t)))) in
    (t', Fst(s, (t, s1)))
  | Snd(s, e1) ->
    let s1 = type_of cfg ctx env e1 in
    let t = (match fst s1 with
     | TTuple(_, r) -> r
     | t -> raise (Type_error (Format.sprintf "Type error at line %d column %d: expected tuple, got %s"
                                 s.startpos.pos_lnum (get_col s.startpos) (string_of_typ t)))) in
    (t, Snd(s, s1))
  | Tup(s, e1, e2) ->
    let t1 = type_of cfg ctx env e1 in
    let t2 = type_of cfg ctx env e2 in
    (TTuple(fst t1, fst t2), Tup(s, t1, t2))
  | Int(src, sz, v) ->
    if v >= 1 lsl sz then
      (raise (Type_error (Format.sprintf "Type error at line %d column %d: integer constant out of range"
                           src.startpos.pos_lnum (get_col src.startpos)))) else ();
    (TInt(sz), Int(src, sz, v))
  | Discrete(src, l) ->
    let sum = List.fold (List.map l Bignum.to_float) ~init:0.0 ~f:(fun acc i -> acc +. i) in
    if not (within_epsilon sum 1.0) then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: discrete parameters must sum to 1, got %f"
                           src.startpos.pos_lnum (get_col src.startpos) sum))
    else (TInt(num_binary_digits ((List.length l) - 1)), Discrete(src, l))
  | LeftShift(s, e1, i) ->
    let (t, e) = type_of cfg ctx env e1 in
    (t, LeftShift(s, (t, e), i))
  | RightShift(s, e1, i) ->
    let (t, e) = type_of cfg ctx env e1 in
    (t, RightShift(s, (t, e), i))
  | Eq(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun s1 s2 -> Eq(s, s1, s2)) s.startpos e1 e2 "="))
  | Lt(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Lt(s, e1, e2)) s.startpos e1 e2 "<"))
  | Gt(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Gt(s, e1, e2)) s.startpos e1 e2 ">"))
  | Lte(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Lte(s, e1, e2)) s.startpos e1 e2 "<="))
  | Gte(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Gte(s, e1, e2)) s.startpos e1 e2 ">="))
  | Neq(s, e1, e2) -> (TBool, snd (expect_compatible_int (fun e1 e2 -> Neq(s, e1, e2)) s.startpos e1 e2 "!="))
  | Plus(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Plus(s, e1, e2)) s.startpos e1 e2 "+" in
    (TInt(sz), res)
  | Minus(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Minus(s, e1, e2)) s.startpos e1 e2 "-" in
    (TInt(sz), res)
  | Mult(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Mult(s, e1, e2)) s.startpos e1 e2 "*" in
    (TInt(sz), res)
  | Div(s, e1, e2) ->
    let sz, res = expect_compatible_int (fun e1 e2 -> Div(s, e1, e2)) s.startpos e1 e2 "/" in
    (TInt(sz), res)
  | Let(slet, x, e1, e2) ->
    let r1 = type_of cfg ctx env e1 in
    let r2 = type_of cfg ctx (Map.Poly.set env ~key:x ~data:(fst r1)) e2 in
    (fst r2, Let(slet, x, r1, r2))
  | Ite(s, g, thn, els) ->
    let sg = expect_t g ((EG.get_src g).startpos) TBool in
    let (t1, thnbody) = type_of cfg ctx env thn and (t2, elsbody) = type_of cfg ctx env els in
    if not (type_eq t1 t2) then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: expected equal types \
                                         from branches of if-statement, got %s and %s"
                           s.startpos.pos_lnum (get_col s.startpos) (string_of_typ t1) (string_of_typ t2)))
    else (t1, Ite(s, sg, (t1, thnbody), (t2, elsbody)))
  | FuncCall(s, "nth_bit", [Int(src, sz, v); e2]) ->
    let conve2 = match type_of cfg ctx env e2 with
      | (TInt(v), r) ->(TInt(v), r)
      | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: expected int for second argument"
                                  s.startpos.pos_lnum (get_col s.startpos))) in
    (TBool, FuncCall(s, "nth_bit", [(TInt(v), Int(src, sz, v)); conve2]))
  | FuncCall(s, id, args) ->
    let res = try Map.Poly.find_exn env id
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could not find function \
                                                   '%s' during typechecking"
                                     s.startpos.pos_lnum (get_col s.startpos) id)) in
    let (targ, tres) = (match res with
        | TFunc(targ, tres) -> targ, tres
        | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: non-function type found for \
                                                   '%s' during typechecking, found %s "
                                     s.startpos.pos_lnum (get_col s.startpos) id (string_of_typ res)))) in
    let zipped = try List.zip_exn args targ
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could incompatible argument length, expected \
                                                   %d arguments and got %d arguments"
                                     s.startpos.pos_lnum (get_col s.startpos) (List.length targ) (List.length args))) in
    let arg' = List.mapi zipped ~f:(fun idx (arg, typ) ->
        let (found_t, body) = type_of cfg ctx env arg in
        if (type_eq found_t typ) then (found_t, body) else
          raise (Type_error (Format.sprintf "Type error in argument %d at line %d column %d: expected type %s, got %s"
                               s.startpos.pos_lnum (get_col s.startpos) (idx + 1) (string_of_typ typ) (string_of_typ found_t)))
      ) in
    (tres, FuncCall(s, id, arg'))
  | IntConst(_, _) -> failwith "Internal Error: unstripped int const"
  | Iter(s, id, init, k) ->
    let res = try Map.Poly.find_exn env id
      with _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: could not find function \
                                                   '%s' during typechecking"
                                     s.startpos.pos_lnum (get_col s.startpos) id)) in
    let (_, tres) = (match res with
        | TFunc(targ, tres) -> targ, tres
        | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: non-function type found for \
                                                   '%s' during typechecking, found %s "
                                     (get_col s.startpos) (get_col s.startpos) id (string_of_typ res)))) in
    let init' = type_of cfg ctx env init in
    (* TODO check arg validity*)
    (tres, Iter(s, id, init', k))
  | Unif (s, sz, b, e) -> 
    if e > 1 lsl sz then
      (raise (Type_error (Format.sprintf "Type error at line %d column %d: integer constant out of range"
                           s.startpos.pos_lnum (get_col s.startpos)))) 
    else (TInt(sz), Unif(s, sz, b, e))
  | Binom (s, sz, n, p) -> 
    if n+1 > 1 lsl sz then 
      (raise (Type_error (Format.sprintf "Type error at line %d column %d: integer constant out of range"
                           s.startpos.pos_lnum (get_col s.startpos)))) 
    else (TInt(sz), Binom(s, sz, n, p))
  | ListLit(s, es) ->
    let len = List.length es in
    if len > cfg.max_list_length then
      raise (Type_error (Format.sprintf "Type error at line %d column %d: \
                                         length of list literal (%d) exceeds maximum list length (%d)"
                          s.startpos.pos_lnum (get_col s.startpos) len cfg.max_list_length))
    else
      let (t, e') = type_of cfg ctx env (List.hd_exn es) in
      (TList t, ListLit(s, (t, e') :: List.map (List.tl_exn es) ~f:(expect_t' t)))
  | ListLitEmpty(s, t) ->
    begin match t with
    | TList _ -> (t, ListLitEmpty s)
    | _ -> raise (Type_error (Format.sprintf "Type error at line %d column %d: empty list must have a list type"
                                s.startpos.pos_lnum (get_col s.startpos)))
    end
  | Cons(s, e1, e2) ->
    let (t, e1') = type_of cfg ctx env e1 in
    (TList t, Cons(s, (t, e1'), expect_t' (TList t) e2))
  | Head(s, e) ->
    let (t, tast) = expect_list e in
    (t, Head(s, tast))
  | Tail(s, e) ->
    let (_, (t, e')) = expect_list e in
    (t, Tail(s, (t, e')))
  | Length(s, e) ->
    let (_, tast) = expect_list e in
    (TInt (bit_length cfg.max_list_length), Length(s, tast))

let rec expand_iter_t s f ((t, curv):tast) k : tast =
  assert (k >= 0);
  if k = 0 then (t, curv) else
    (t, Let(s, "$iterident", (t, FuncCall(s, f, [(t, curv)])),
            expand_iter_t s f (t, Ident(s, "$iterident")) (k-1)))



let rec from_external_typ cfg (t:EG.typ) : CG.typ =
  match t with
    TBool -> TBool
  | TInt(sz) ->
    let l = List.init sz ~f:(fun _ -> CG.TBool) in
    let rec mk_dfs_typ l =
      match l with
      | [x] -> x
      | x::xs ->
        CG.TTuple(x, mk_dfs_typ xs)
      | [] -> failwith "Internal Error: Invalid int type"
    in
    mk_dfs_typ l
  | TTuple(t1, t2) -> TTuple(from_external_typ cfg t1, from_external_typ cfg t2)
  | TList t -> from_external_typ cfg @@
    TTuple(TInt(bit_length cfg.max_list_length),
           Fn.apply_n_times ~n:(cfg.max_list_length - 1) (fun t' -> EG.TTuple(t, t')) t)
  | _ -> failwith "Internal Error: unreachable"

let rec and_of_l l =
  match l with
  | [] -> CG.True
  | [x] -> x
  | x::xs -> CG.And(x, and_of_l xs)

let rec gen_discrete mgr (l: float List.t) =
  let open Cudd in
  let open CG in
  (* first generate the ADD *)
  (* list of bits in little-endian order *)
  let bits = List.init (num_binary_digits ((List.length l) - 1)) ~f:(fun i -> (Ident(Format.sprintf "d%d" i), Bdd.newvar mgr)) in
  let numbits = List.length bits in
  let bitcube = List.fold bits ~init:(Bdd.dtrue mgr) ~f:(fun acc i -> Bdd.dand acc (snd i)) in
  let add = List.foldi l ~init:(Add.cst mgr 0.0) ~f:(fun idx acc param ->
      let bitvec = List.zip_exn (int_to_bin numbits idx) (bits) in
      let indicator = List.fold bitvec ~init:(Bdd.dtrue mgr) ~f:(fun acc (v, (_, b)) ->
          let curv = if v = 1 then b else Bdd.dnot b in
          Bdd.dand acc curv
        ) in
      let leaf = Add.cst mgr param in
      Add.ite indicator leaf acc
    ) in
  (* now make the list of flip assignments *)
  let sum_add a = Add.dval (Add.exist bitcube a) in
  let assgn = fold_with_seen bits ~init:[] ~f:(fun seen acc (cur_name, cur_bit) ->
      let all_assgn = all_assignments mgr seen in
      let l = List.map all_assgn ~f:(fun (cur_constraint, cur_bdd) ->
          let p1 = sum_add (Add.mul add (Add.of_bdd (Bdd.dand cur_bit cur_bdd))) in
          let p2 = sum_add (Add.mul add (Add.of_bdd (Bdd.dand cur_bdd (Bdd.dnot cur_bit)))) in
          if within_epsilon p1 0.0 then
            (cur_constraint, 0.)
          else
            (cur_constraint, (p1 /. (p1 +. p2)))
        ) in
      (* now build the expression *)
      (match l with
       | [] -> failwith "unreachable"
       | [(_, param)] -> [cur_name, Flip((Bignum.of_float_decimal param))]
       | (_, param)::xs ->
         let ifbody = List.fold xs ~init:(Flip((Bignum.of_float_decimal param))) ~f:(fun acc (guard, param) -> Ite(guard, Flip((Bignum.of_float_decimal param)), acc)) in
         [cur_name, ifbody]
      ) @ acc
    ) in
  (* now finally build the entire let assignment *)
  let inner_body = mk_dfs_tuple (List.map bits ~f:fst) in
  List.fold assgn ~init:inner_body ~f:(fun acc (Ident(name), body) -> Let(name, body, acc))


let rec nth_snd i inner =
  assert (i >= 0);
  match i with
    0 -> inner
  | n -> CG.Snd (nth_snd (n-1) inner)

let nth_bit sz n e : CG.expr =
  assert (n < sz && n >= 0);
  if n = sz-1 then nth_snd n (e) else Fst(nth_snd n (e))

let gen_adder sz a b : CG.expr =
  let a_name = fresh () in
  let b_name = fresh () in
  let tmp_a = CG.Ident(a_name) in
  let tmp_b = CG.Ident(b_name) in
  let carryname = Format.sprintf "carry%s" (fresh ()) in
  let outputname = Format.sprintf "output%s" (fresh ()) in
  let halfout = (Format.sprintf "%s_0" outputname, CG.Xor(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  let halfcarry = (Format.sprintf "%s_0" carryname, CG.And(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  (* very finnicky business in here ... generate a sequence of full adders
     that feed one into the next *)
  let fulladders = List.init (sz - 1) ~f:(fun bit ->
      let curidx = bit + 1 in
      let curbit = sz - bit - 2 in
      let curout = Format.sprintf "%s_%d" outputname curidx in
      let curinput_a = nth_bit sz curbit tmp_a in
      let curinput_b = nth_bit sz curbit tmp_b in
      let prevcarry = Format.sprintf "%s_%d" carryname (curidx - 1) in
      let curcarry = Format.sprintf "%s_%d" carryname curidx in
      [(curout, CG.Xor(Ident(prevcarry), CG.Xor(curinput_a, curinput_b)));
       (curcarry, CG.Or(CG.And(Ident(prevcarry), curinput_a),
                        CG.Or(CG.And(Ident(prevcarry), curinput_b), CG.And(curinput_a, curinput_b))))]
    ) |> List.concat in
  let full_l = [(a_name, a); (b_name, b); halfout; halfcarry] @ fulladders in
  let output_list = List.init sz ~f:(fun idx -> CG.Ident(Format.sprintf "%s_%d" outputname (sz - 1 - idx))) in
  let inner = mk_dfs_tuple output_list in
  List.fold_right full_l ~init:inner ~f:(fun (name, e) acc -> CG.Let(name, e, acc))

(* generates a subtractor circuit for a - b *)
let gen_subtractor sz a b : CG.expr =
  let a_name = fresh () in
  let b_name = fresh () in
  let tmp_a = CG.Ident(a_name) in
  let tmp_b = CG.Ident(b_name) in
  let borrowname = Format.sprintf "borrow%s" (fresh ()) in
  let outputname = Format.sprintf "output%s" (fresh ()) in
  let halfout = (Format.sprintf "%s_0" outputname, CG.Xor(nth_bit sz (sz-1) tmp_a, nth_bit sz (sz-1) tmp_b)) in
  let halfborrow = (Format.sprintf "%s_0" borrowname, CG.And(Not(nth_bit sz (sz-1) tmp_a), nth_bit sz (sz-1) tmp_b)) in
  (* very finnicky business in here ... generate a sequence of full adders
     that feed one into the next *)
  let fullsubt = List.init (sz - 1) ~f:(fun bit ->
      let curidx = bit + 1 in
      let curbit = sz - bit - 2 in
      let curout = Format.sprintf "%s_%d" outputname curidx in
      let curinput_a = nth_bit sz curbit tmp_a in
      let curinput_b = nth_bit sz curbit tmp_b in
      let prevborrow = Format.sprintf "%s_%d" borrowname (curidx - 1) in
      let curborrow = Format.sprintf "%s_%d" borrowname curidx in
      [(curout, CG.Xor(Ident(prevborrow), CG.Xor(curinput_a, curinput_b)));
       (curborrow, CG.Or(CG.And(Ident(prevborrow), Not(curinput_a)),
                        CG.Or(CG.And(Ident(prevborrow), curinput_b), CG.And(Not(curinput_a), curinput_b))))]
    ) |> List.concat in
  let full_l = [(a_name, a); (b_name, b); halfout; halfborrow] @ fullsubt in
  let output_list = List.init sz ~f:(fun idx -> CG.Ident(Format.sprintf "%s_%d" outputname (sz - 1 - idx))) in
  let inner = mk_dfs_tuple output_list in
  List.fold_right full_l ~init:inner ~f:(fun (name, e) acc -> CG.Let(name, e, acc))

let extract_sz t =
  (match t with
   | EG.TInt(sz) -> sz
   | _ -> failwith "Internal Type Error: expected int")

let extract_elem_type = function
| EG.TList t -> t
| _ -> failwith "Internal Type Error: expected list type"

let rec gen_default_core =
  let open CG in
  function
  | TBool -> False
  | TTuple(t1, t2) -> Tup(gen_default_core t1, gen_default_core t2)

let unreachable_core e = CG.Let("$_", Observe False, e)

type external_ctx = Cudd.Man.dt

let rec from_external_expr_h (ctx: external_ctx) (cfg: config) ((t, e): tast) : CG.expr =
  let list_len_bits = bit_length cfg.max_list_length in
  let list_len_type = EG.TInt list_len_bits in
  let mk_length_int x = (list_len_type, Int(EG.gen_src, list_len_bits, x)) in
  let gen_list_lit es =
    let len = List.length es in
    let length_core = from_external_expr_h ctx cfg @@ mk_length_int len in
    let elems_core = List.map es ~f:(from_external_expr_h ctx cfg) in
    let defaults_core = List.init (cfg.max_list_length - len)
      ~f:(Fn.const @@ gen_default_core @@ from_external_typ cfg @@ extract_elem_type t) in
    CG.Tup(length_core, mk_dfs_tuple (elems_core @ defaults_core)) in
  let max_length_int = mk_length_int cfg.max_list_length in
  let gen_get_length xs =
    (* NOTE: the TBool here isn't actually the correct type but since we are
     * just doing Fst on an Ident it doesn't matter. *)
    (list_len_type, Fst(EG.gen_src, (TTuple(list_len_type, TBool), Ident(EG.gen_src, xs)))) in
  let gen_check_empty elem_t xs res =
    CG.Ite(
      from_external_expr_h ctx cfg
        (TBool, Eq(EG.gen_src, gen_get_length xs, mk_length_int 0)),
      unreachable_core @@ gen_default_core @@ from_external_typ cfg elem_t,
      res) in
  let gen_eval_arg e f =
    let x = fresh () in
    CG.Let(x, from_external_expr_h ctx cfg e, f x) in
  match e with
  | And(_, e1, e2) ->
    let s1 = from_external_expr_h ctx cfg e1 in
    let s2 = from_external_expr_h ctx cfg e2 in And(s1, s2)
  | Or(_, e1, e2) ->
    let s1 = from_external_expr_h ctx cfg e1 in
    let s2 = from_external_expr_h ctx cfg e2 in Or(s1, s2)
  | Iff(_, e1, e2) ->
    let s1 = from_external_expr_h ctx cfg e1 in
    let s2 = from_external_expr_h ctx cfg e2 in Eq(s1, s2)
  | Xor(_, e1, e2) ->
    let s1 = from_external_expr_h ctx cfg e1 in
    let s2 = from_external_expr_h ctx cfg e2 in Xor(s1, s2)
  | LeftShift(_, e, 0) -> from_external_expr_h ctx cfg e
  | LeftShift(_, e, amt) ->
    let sube = from_external_expr_h ctx cfg e in
    assert (amt > 0);
    let sz = extract_sz t in
    let id = Format.sprintf "leftshift_%s" (fresh ()) in
    let rec h depth : CG.expr =
      if depth = sz - 1 then False
      else if depth + amt >= sz then Tup(False, h (depth+1))
      else Tup(nth_bit sz (depth+amt) (Ident(id)), h (depth+1)) in
    Let(id, sube, h 0)
  | RightShift(_, e, 0) -> from_external_expr_h ctx cfg e
  | RightShift(_, e, amt) ->
    assert (amt > 0);
    let sube = from_external_expr_h ctx cfg e in
    let sz = extract_sz t in
    let id = Format.sprintf "rightshift_%s" (fresh ()) in
    let rec h depth : CG.expr =
      if depth = sz - 1 then
        if (depth - amt < 0) then False else nth_bit sz (depth - amt) (Ident(id))
      else if depth < amt || amt >= sz then Tup(False, h (depth+1))
      else Tup(nth_bit sz (depth - amt) (Ident(id)), h (depth+1)) in
    Let(id, sube, h 0)
  | Plus(_, e1, e2) ->
    let sz = extract_sz (fst e1) in
    gen_adder sz (from_external_expr_h ctx cfg e1) (from_external_expr_h ctx cfg e2)
  | Minus(_, e1, e2) ->
    let sz = extract_sz t in
    gen_subtractor sz (from_external_expr_h ctx cfg e1) (from_external_expr_h ctx cfg e2)
  | Eq(_, (t1, e1), (t2, e2)) ->
    let sz = extract_sz t1 in
    let n1 = fresh () and n2 = fresh () in
    let inner = List.init sz ~f:(fun idx ->
        CG.Eq(nth_bit sz idx (Ident(n1)), nth_bit sz idx (Ident(n2)))
      ) |> and_of_l in
    Let(n1, from_external_expr_h ctx cfg (t1, e1),
        Let(n2, from_external_expr_h ctx cfg (t2, e2), inner))
  | Neq(s, e1, e2) -> from_external_expr_h ctx cfg (TBool, Not(s, (TBool, Eq(s, e1, e2))))
  | Mult(s, e1, e2) ->
    let sz = extract_sz (fst e1) in
    let sube1 = from_external_expr_h ctx cfg e1 in
    let sube2 = from_external_expr_h ctx cfg e2 in
    let fresha = Format.sprintf "multa_%s" (fresh ()) in
    let freshb = Format.sprintf "multb_%s" (fresh ()) in
    let freshout = Format.sprintf "multo_%s" (fresh ()) in
    let lst : CG.expr List.t = List.init sz ~f:(fun i ->
        let subadd = from_external_expr_h ctx cfg
            (t, Plus(s, (t, Ident(s, freshout)), (t, LeftShift(s, (t, Ident(s, freshb)), i)))) in
        CG.Ite(nth_bit sz (sz - i - 1) (Ident(fresha)), subadd, Ident(freshout))
      ) in
    let assgn = List.fold (List.rev lst) ~init:(CG.Ident(freshout)) ~f:(fun acc i ->
        Let(freshout, i, acc)) in
    let zeroconst = from_external_expr_h ctx cfg (TInt(sz), Int(s, sz, 0)) in
    Let(freshout, zeroconst,
        Let(fresha, sube1,
            Let(freshb, sube2, assgn)))
  | Div(_, _, _) -> failwith "not implemented /"
  | Lt(_, (t1, e1), (t2, e2)) ->
    let sz = extract_sz t1 in
    let n1 = fresh () and n2 = fresh () in
    let rec h idx : CG.expr =
      if idx >= sz then False
      else Ite(And(nth_bit sz idx (Ident(n1)), Not(nth_bit sz idx (Ident n2))),
               False,
               Ite(And(Not(nth_bit sz idx (Ident(n1))), nth_bit sz idx (Ident n2)), True,
               h (idx + 1))) in
    Let(n1, from_external_expr_h ctx cfg (t1, e1), Let(n2, from_external_expr_h ctx cfg (t2, e2), h 0))
  | Lte(s, (e1t, e1), (e2t, e2)) -> from_external_expr_h ctx cfg (TBool, 
      (* create temporary identifiers to resolve the issue with comparing two uniforms *)
      let e1name = fresh () in
      let e2name = fresh () in
      Let(s, e1name, (e1t, e1), (
        (TBool, Let(s, e2name, (e2t, e2), (
          (TBool, Or(s, (TBool, Lt(s, (e1t, Ident(s, e1name)), (e2t, Ident(s, e2name)))), 
          (TBool, Eq(s, (e1t, Ident(s, e1name)), (e2t, Ident(s, e2name)))))))
        )))
      ))
  | Gt(s, e1, e2) -> from_external_expr_h ctx cfg (TBool, Not(s, (TBool, Lte(s, e1, e2))))
  | Gte(s, e1, e2) -> from_external_expr_h ctx cfg (TBool, Not(s, (TBool, Lt(s, e1, e2))))
  | Not(_, e) -> Not(from_external_expr_h ctx cfg e)
  | Flip(_, f) -> Flip(f)
  | Ident(_, s) -> Ident(s)
  | Discrete(_, l) -> gen_discrete ctx (List.map l Bignum.to_float)
  | Unif(s, sz, b, e) -> 
	  assert(b >= 0);
	  assert(e > b);
	  if b > 0 then from_external_expr_h ctx cfg (TInt(sz), Plus(s, (TInt(sz), Int(s, sz, b)), (TInt(sz), Unif(s, sz, 0, e-b)))) else
	  let rec make_flip_list bit_count length = 
		  if length = 0 then []
		  else if length > bit_count then CG.False :: (make_flip_list bit_count (length-1))
		  else CG.Flip(Bignum.(1 // 2)) :: (make_flip_list bit_count (length-1)) in
	  let make_simple_unif bit_count length = 
		  mk_dfs_tuple (make_flip_list bit_count length) in 
	  let is_power_of_two num = 
	  	(num land (num-1) = 0) in (* no zero check *) 
	  if is_power_of_two e then
		  let num_size = num_binary_digits e-1 in
		  make_simple_unif num_size sz
	  else
		  let power_lt_float = 2.0 ** (float_of_int((num_binary_digits e) - 1)) in
		  let power_lt_int = int_of_float power_lt_float in 
		  from_external_expr_h ctx cfg 
			  (TInt(sz), Ite(s, 	(TBool, Flip(s, Bignum.(power_lt_int // e))), 
								  (TInt(sz), Unif(s, sz, 0, power_lt_int)), 
								  (TInt(sz), Unif(s, sz, power_lt_int, e))))
  | Binom(s, sz, n, p) -> 
    assert(n >= 0);
    let t = EG.TInt(sz) in
    let intone = (t, Int(s, sz, 1)) in
    let intzero = (t, Int(s, sz, 0)) in
    let ident = (t, Ident(s, "$binomexp")) in
    let flip = (EG.TBool, Flip(s, p)) in
    let rec make_binom_let k = 
      if k = 0 then ident
      else 
        (t, Let(s, "$binomexp", (t, Ite(s, flip,   
          (t, Plus(s, intone, ident)), 
          ident)), make_binom_let(k-1))) in
    if n = 0 then from_external_expr_h ctx cfg intzero else 
    from_external_expr_h ctx cfg 
      (t, Let(s, "$binomexp", (t, Ite(s, flip, intone, intzero)), make_binom_let(n-1)))   
  | Int(_, sz, v) ->
    let bits = int_to_bin sz v
               |> List.map ~f:(fun i -> if i = 1 then CG.True else CG.False) in
    mk_dfs_tuple bits
  | True(_) -> True
  | False(_) -> False
  | Observe(_, e) ->
    Observe(from_external_expr_h ctx cfg e)
  | Let(_, x, e1, e2) ->
    Let(x, from_external_expr_h ctx cfg e1, from_external_expr_h ctx cfg e2)
  | Ite(_, g, thn, els) -> Ite(from_external_expr_h ctx cfg g,
                               from_external_expr_h ctx cfg thn,
                               from_external_expr_h ctx cfg els)
  | Snd(_, e) -> Snd(from_external_expr_h ctx cfg e)
  | Fst(_, e) -> Fst(from_external_expr_h ctx cfg e)
  | Tup(_, e1, e2) -> Tup(from_external_expr_h ctx cfg e1, from_external_expr_h ctx cfg e2)
  | FuncCall(src, "nth_bit", [(_, Int(_, sz, v)); e2]) ->
    if v >= sz then
      (raise (EG.Type_error (Format.sprintf "Type error at line %d column %d: nth_bit exceeds maximum bit size"
                               src.startpos.pos_lnum (get_col src.startpos))));
    let internal = from_external_expr_h ctx cfg e2 in
    nth_bit sz v internal
  | FuncCall(_, id, args) -> FuncCall(id, List.map args ~f:(fun i -> from_external_expr_h ctx cfg i))
  | Iter(s, f, init, k) ->
    (* let e = from_external_expr_h ctx cfg init in
     * List.fold (List.init k ~f:(fun _ -> ())) ~init:e
     *   ~f:(fun acc _ -> FuncCall(f, [acc])) *)

    let expanded = expand_iter_t s f init k in
    from_external_expr_h ctx cfg expanded
  | Sample(_, e) -> Sample(from_external_expr_h ctx cfg e)
  | IntConst(_, _) -> failwith "not implemented"
  | ListLit(_, es) -> gen_list_lit es
  | ListLitEmpty _ -> gen_list_lit []
  | Cons(s, e1, e2) ->
    gen_eval_arg e1 @@ fun x ->
      gen_eval_arg e2 @@ fun xs ->
        let length_core =
          (* if fst xs == max_list_length then max_list_length else (fst xs) + 1 *)
          let length_xs = gen_get_length xs in
          from_external_expr_h ctx cfg
            (list_len_type, Ite(s,
              (TBool, Eq(s, length_xs, max_length_int)),
              max_length_int,
              (list_len_type, Plus(s, length_xs, mk_length_int 1)))) in
        let rec build_res_core i prev_tup =
          let tup = CG.Snd prev_tup in
          let elem = CG.Fst tup in
          if i = cfg.max_list_length - 1 then elem else
            CG.Tup(elem, build_res_core (succ i) tup) in
        let res_core =
          if cfg.max_list_length = 1 then CG.Ident x else
            CG.Tup(CG.Ident x, build_res_core 1 (CG.Ident xs)) in
        Tup(length_core, res_core)
  | Head(_, e) ->
    gen_eval_arg e @@ fun xs ->
      let list_part = CG.Snd (Ident xs) in
      gen_check_empty (extract_elem_type (fst e)) xs @@
        if cfg.max_list_length = 1 then list_part else Fst list_part
  | Tail(s, e) ->
    gen_eval_arg e @@ fun xs ->
      let length_core = from_external_expr_h ctx cfg
        (list_len_type, Minus(s, gen_get_length xs, mk_length_int 1)) in
      let default_core = gen_default_core @@
        from_external_typ cfg @@ extract_elem_type t in
      let rec build_res_core i prev_tup =
        let tup = CG.Snd prev_tup in
        if i = cfg.max_list_length - 1 then
          CG.Tup(tup, default_core)
        else
          CG.Tup(CG.Fst tup, build_res_core (succ i) tup) in
      let res_core =
        if cfg.max_list_length = 1 then default_core else
          build_res_core 1 @@ CG.Snd (CG.Ident xs) in
      gen_check_empty t xs @@ Tup(length_core, res_core)
  | Length(_, e) -> Fst (from_external_expr_h ctx cfg e)

let from_external_expr mgr cfg in_func (env: EG.tenv) (e: EG.eexpr) : (EG.typ * CG.expr) =
  let ctx = if in_func then {in_func=true} else {in_func=false} in
  let (typ, e) = type_of cfg ctx env e in
  let r = (typ, from_external_expr_h mgr cfg (typ, e)) in
  r

let from_external_arg cfg (a:EG.arg) : CG.arg =
  let (name, t) = a in
  (name, from_external_typ cfg t)

let check_return_type (f: EG.func) (t : EG.typ) : unit =
  let open EG in
  match f.return_type with
  | Some declared when not (type_eq declared t) ->
    let src = get_src f.body in
    raise (Type_error (Format.sprintf "Type error at line %d column %d: declared return type %s \
                                       of function '%s' does not match inferred type %s"
                       src.startpos.pos_lnum (get_col src.startpos) (string_of_typ declared)
                       f.name (string_of_typ t)))
  | _ -> ()

let from_external_func mgr cfg (tenv: EG.tenv) (f: EG.func) : (EG.typ * CG.func) =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let (t, conv) = from_external_expr mgr cfg true tenvwithargs f.body in
  check_return_type f t;
  (* convert arguments *)
  let args = List.map f.args ~f:(from_external_arg cfg) in
  (TFunc(List.map f.args ~f:snd, t), {name = f.name;
       args = args;
       body = conv})

let from_external_func_optimize mgr cfg (tenv: EG.tenv) (f: EG.func) (flip_lifting: bool) (branch_elimination: bool) (determinism: bool) : (EG.typ * CG.func) =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let (t, conv) = from_external_expr mgr cfg true tenvwithargs f.body in
  check_return_type f t;
  let optbody = Optimization.do_optimize conv !n flip_lifting branch_elimination determinism in
  (* convert arguments *)
  let args = List.map f.args ~f:(from_external_arg cfg) in
  (TFunc(List.map f.args ~f:snd, t), {name = f.name;
        args = args;
        body = optbody})

let from_external_prog ?(cfg: config = default_config) (p: EG.program) : (EG.typ * CG.program) =
  let mgr = Cudd.Man.make_d () in
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let (t, conv) = from_external_func mgr cfg tenv i in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let (t, convbody) = from_external_expr mgr cfg false tenv p.body in
  (t, {functions = functions; body = convbody})

let from_external_prog_optimize ?(cfg: config = default_config) (p: EG.program) (flip_lifting: bool) (branch_elimination: bool) (determinism: bool) : (EG.typ * CG.program) =
  let mgr = Cudd.Man.make_d () in
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let (t, conv) = from_external_func_optimize mgr cfg tenv i flip_lifting branch_elimination determinism in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let (t, convbody) = from_external_expr mgr cfg false tenv p.body in
  let optbody = Optimization.do_optimize convbody !n flip_lifting branch_elimination determinism in
  (t, {functions = functions; body = optbody})
