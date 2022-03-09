(** Performs optimization passes over the core grammar **)
open Core
open Util
module EG = ExternalGrammar
module CG = CoreGrammar
module LF = LogicalFormula

type config = { max_list_length: int }

let default_recursion_limit = 10

let default_config = { max_list_length = default_recursion_limit }

let n = ref 0

let fresh () =
  n := !n + 1;
  (Format.sprintf "$%d" !n)

let flip_id = ref 1

let within_epsilon x y =
  (Float.compare (Float.abs (x -. y)) 0.0001) < 0

type env = (String.t, LF.expr) Map.Poly.t (* map from variable identifiers to Logical Formula*)

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
    | Binom(_, _, n, _) -> LogProbability.make (float_of_int (n+1))
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

let num_binary_digits d = int_of_float (Float.round_down (Util.log2 (float_of_int (d)))) + 1

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

let gen_discrete mgr (l: float List.t) =
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

let gen_discrete_sbk (l: float List.t) (priority: (float * int) List.t option) =
  let open Cudd in
  let open CG in
  let max = (List.length l) - 1 in
  let len = num_binary_digits max in
  let get_tuples v = 
    int_to_bin len v
      |> List.map  ~f:(fun i -> if i = 1 then True else False)
      |> mk_dfs_tuple
  in
  let sift_priority (l: (int * float) List.t) (priority: (float * int) List.t) : (int * float) List.t = 
    List.sort l ~compare: (fun (_, p1) (_, p2) -> 
      let c1 = List.Assoc.find priority ~equal: (fun f1 f2 -> Float.equal f1 f2) p1 in
      let c2 = List.Assoc.find priority ~equal: (fun f1 f2 -> Float.equal f1 f2) p2 in
      let order = match c1, c2 with
        | None, None -> 0
        | None, _ -> -1
        | _, None -> 1
        | Some(c_1), Some(c_2) -> 
          let diff = Poly.descending c_1 c_2 in
          if diff = 0 then
            Poly.descending p1 p2
          else
            diff
      in
      order)
  in

  let rec get_idx_prob (l: float List.t) (idx: int) (rest: (int * float) List.t): (int * float) List.t =
    match l with
    | [] -> List.rev_append rest []
    | head::tail -> 
      if Float.equal head 0.0 then
        get_idx_prob tail (idx + 1) rest 
      else
        get_idx_prob tail (idx + 1) ((idx, head)::rest)
  in

  let idxProb = get_idx_prob l 0 [] in
  let sorted_probs = 
    match priority with
    (* Heuristic: gen flips in order of large to small probabilities *)
    | None -> List.sort idxProb ~compare: (fun (_, p1) (_, p2) -> Poly.descending p1 p2) 
    (* Heuristic: choose priority flips to do first *)
    | Some(p) -> 
      sift_priority idxProb p 
  in
  let probs_length = List.length sorted_probs in
  let probs, _ = List.foldi sorted_probs ~init: ([], 0.0) ~f:(fun idx (probs, total) (i, p) -> 
    if idx = probs_length - 1 then
      ((i, fresh(), 1.0)::probs, total +. p)
    else
      ((i, fresh(), p /. (1. -. total))::probs, total +. p))
  in
  let (inner_idx, _, _) = 
    match List.hd probs with
    | None -> failwith "Discrete with no values"
    | Some(i, x, p) -> i, x, p 
  in
  let inner_body = get_tuples inner_idx in 
  let final_ident = fresh() in
  let final_body = List.foldi probs ~init: inner_body ~f: (fun idx acc (i, x, _) -> 
    if idx = 0 then
      (get_tuples i)
    else
      Ite(Ident(x), (get_tuples i), acc))
  in
  let final_expr = Let(final_ident, final_body, Ident(final_ident)) in
  let e = List.foldi (List.rev_append probs []) ~init: final_expr ~f: (fun idx acc (_, x, p) ->
    if idx = max then
      acc
    else
      Let(x, Flip((Bignum.of_float_decimal p)), acc))
  in
  e

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
  (* Format.printf "converting %s\n" (string_of_tast (t,e));
   * flush_all (); *)
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
  | Lte(s, e1, e2) -> from_external_expr_h ctx cfg (TBool, Or(s, (TBool, Lt(s, e1, e2)), (TBool, Eq(s, e1, e2))))
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

type tree = 
  | Node of (float * int) List.t option * tree * tree * tree
  | Branch of tree * tree
  | Leaf 

let from_external_expr_h_sbk (ctx: external_ctx) (cfg: config) ((t, e): tast) : CG.expr =
  let rec merge_uniq l1 l2 l3 = 
    match l1 with
    | [] -> List.rev_append l3 l2
    | head::tail -> 
      let uniq = if List.mem l2 head ~equal: Poly.equal then l3 else head::l3 in
      merge_uniq tail l2 uniq
  in
  let largest_count (tbl: (float * int) List.t) : (float * int) List.t =
    List.sort tbl ~compare:(fun (_, v1) (_, v2) -> Poly.descending v1 v2) 
  in
  let rec annotate ((_, e): tast) : float List.t * tree =
    match e with
    | And(_, e1, e2) | Or(_, e1, e2) | Iff(_, e1, e2) | Xor(_, e1, e2) | Plus(_, e1, e2) | Minus(_, e1, e2)
    | Eq(_, e1, e2) | Neq(_, e1, e2) | Mult(_, e1, e2) | Lt(_, e1, e2) | Lte(_, e1, e2) | Gt(_, e1, e2)
    | Gte(_, e1, e2) | Tup(_, e1, e2) | Let(_, _, e1, e2) ->
      let f1, t1 = annotate e1 in
      let f2, t2 = annotate e2 in
      (merge_uniq f1 f2 []), Branch(t1, t2)
    | Not(_, e) -> annotate e
      (* (match e with 
      | Flip(f) -> [1.0 -. f], Leaf
      | _ -> annotate e) *)
    | LeftShift(_, e, _) | RightShift(_, e, _) | Observe(_, e) | Snd(_, e) | Fst(_, e) | Sample(_, e) | Length(_, e) -> 
      annotate e 
    | FuncCall(_, "nth_bit", [(_, Int(_, _, _)); e2]) -> annotate e2
    | Flip(_, f) -> [(Bignum.to_float f)], Leaf
    | Discrete(_, l) -> 
      (List.dedup_and_sort ~compare: Poly.compare (List.map l ~f:(fun a -> Bignum.to_float(a)))), Leaf
    | Ident(_, _) | Int(_, _, _) | True(_) | False(_) | Iter(_, _, _, _)
    | ListLit(_, _) | ListLitEmpty _ | Cons(_, _, _) | Head(_, _) | Tail(_, _) | FuncCall(_, _, _) -> [], Leaf
    | Ite(_, g, thn, els) -> 
      let f1, t1 = annotate g in
      let f2, t2 = annotate thn in
      let f3, t3 = annotate els in
      let counts = Hashtbl.create (module Float) in
      let update_tbl f = Hashtbl.update counts f ~f:(fun co -> match co with None -> 1 | Some(c) -> c + 1) in
      List.iter f2 ~f: update_tbl;
      List.iter f3 ~f: update_tbl;
      let lst = Hashtbl.to_alist counts in
      let largest_prob = match lst with _::_ -> Some(largest_count lst) | [] -> None in     
      (merge_uniq f1 (f2@f3) []), Node(largest_prob, t1, t2, t3)
    | IntConst(_, _) -> failwith "not implemented"
    | Div(_, _, _) -> failwith "not implemented"
    | Unif (_, _, _, _) | Binom (_, _, _, _) -> failwith "not implemented"
  in

  let rec from_external_expr_h_sbk_e (ctx: external_ctx) (cfg: config) (ann: tree) (prob: (float * int) List.t option) ((t, e): tast) : CG.expr =
    let list_len_bits = bit_length cfg.max_list_length in
    let list_len_type = EG.TInt list_len_bits in
    let mk_length_int x = (list_len_type, Int(EG.gen_src, list_len_bits, x)) in
    let gen_list_lit es =
      let len = List.length es in
      let length_core = from_external_expr_h_sbk_e ctx cfg ann prob @@ mk_length_int len in
      let elems_core = List.map es ~f:(from_external_expr_h_sbk_e ctx cfg ann prob) in
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
        from_external_expr_h_sbk_e ctx cfg ann prob
          (TBool, Eq(EG.gen_src, gen_get_length xs, mk_length_int 0)),
        unreachable_core @@ gen_default_core @@ from_external_typ cfg elem_t,
        res) in
    let gen_eval_arg e f =
      let x = fresh () in
      CG.Let(x, from_external_expr_h_sbk_e ctx cfg ann prob e, f x) in
    match e with
    | And(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in And(s1, s2)
    | Or(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in Or(s1, s2)
    | Iff(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in Eq(s1, s2)
    | Xor(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in Xor(s1, s2)
    | LeftShift(_, e, 0) -> from_external_expr_h_sbk_e ctx cfg ann prob e
    | LeftShift(_, e, amt) ->
      let sube = from_external_expr_h_sbk_e ctx cfg ann prob e in
      assert (amt > 0);
      let sz = extract_sz t in
      let id = Format.sprintf "leftshift_%s" (fresh ()) in
      let rec h depth : CG.expr =
        if depth = sz - 1 then False
        else if depth + amt >= sz then Tup(False, h (depth+1))
        else Tup(nth_bit sz (depth+amt) (Ident(id)), h (depth+1)) in
      Let(id, sube, h 0)
    | RightShift(_, e, 0) -> from_external_expr_h_sbk_e ctx cfg ann prob e
    | RightShift(_, e, amt) ->
      assert (amt > 0);
      let sube = from_external_expr_h_sbk_e ctx cfg ann prob e in
      let sz = extract_sz t in
      let id = Format.sprintf "rightshift_%s" (fresh ()) in
      let rec h depth : CG.expr =
        if depth = sz - 1 then
          if (depth - amt < 0) then False else nth_bit sz (depth - amt) (Ident(id))
        else if depth < amt || amt >= sz then Tup(False, h (depth+1))
        else Tup(nth_bit sz (depth - amt) (Ident(id)), h (depth+1)) in
      Let(id, sube, h 0)
    | Plus(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let sz = extract_sz (fst e1) in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in
      gen_adder sz s1 s2
    | Minus(_, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let sz = extract_sz (fst e1) in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in
      gen_subtractor sz s1 s2
    | Eq(_, (t1, e1), (t2, e2)) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let sz = extract_sz t1 in
      let n1 = fresh () and n2 = fresh () in
      let inner = List.init sz ~f:(fun idx ->
          CG.Eq(nth_bit sz idx (Ident(n1)), nth_bit sz idx (Ident(n2)))
        ) |> and_of_l in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob (t1, e1) in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob (t2, e2) in
      Let(n1, s1,
          Let(n2, s2, inner))
    | Neq(s, e1, e2) -> from_external_expr_h_sbk_e ctx cfg ann prob (TBool, Not(s, (TBool, Eq(s, e1, e2))))
    | Mult(s, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let sz = extract_sz (fst e1) in
      let sube1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let sube2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in
      let fresha = Format.sprintf "multa_%s" (fresh ()) in
      let freshb = Format.sprintf "multb_%s" (fresh ()) in
      let freshout = Format.sprintf "multo_%s" (fresh ()) in
      let lst : CG.expr List.t = List.init sz ~f:(fun i ->
          let subadd = from_external_expr_h_sbk_e ctx cfg (Branch(Leaf, Leaf)) prob
              (t, Plus(s, (t, Ident(s, freshout)), (t, LeftShift(s, (t, Ident(s, freshb)), i)))) in
          CG.Ite(nth_bit sz (sz - i - 1) (Ident(fresha)), subadd, Ident(freshout))
        ) in
      let assgn = List.fold (List.rev lst) ~init:(CG.Ident(freshout)) ~f:(fun acc i ->
          Let(freshout, i, acc)) in
      let zeroconst = from_external_expr_h_sbk_e ctx cfg Leaf prob (TInt(sz), Int(s, sz, 0)) in
      Let(freshout, zeroconst,
          Let(fresha, sube1,
              Let(freshb, sube2, assgn)))
    | Div(_, _, _) -> failwith "not implemented /"
    | Lt(_, (t1, e1), (t2, e2)) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let sz = extract_sz t1 in
      let n1 = fresh () and n2 = fresh () in
      let rec h idx : CG.expr =
        if idx >= sz then False
        else Ite(And(nth_bit sz idx (Ident(n1)), Not(nth_bit sz idx (Ident n2))),
                False,
                Ite(And(Not(nth_bit sz idx (Ident(n1))), nth_bit sz idx (Ident n2)), True,
                h (idx + 1))) in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob (t1, e1) in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob (t2, e2) in
      Let(n1, s1, Let(n2, s2, h 0))
    | Lte(s, e1, e2) -> 
      from_external_expr_h_sbk_e ctx cfg (Branch(ann, ann)) prob (TBool, Or(s, (TBool, Lt(s, e1, e2)), (TBool, Eq(s, e1, e2))))
    | Gt(s, e1, e2) -> from_external_expr_h_sbk_e ctx cfg ann prob (TBool, Not(s, (TBool, Lte(s, e1, e2))))
    | Gte(s, e1, e2) -> from_external_expr_h_sbk_e ctx cfg ann prob (TBool, Not(s, (TBool, Lt(s, e1, e2))))
    | Not(_, e) -> Not(from_external_expr_h_sbk_e ctx cfg ann prob e)
    | Flip(_, f) -> Flip(f)
    | Ident(_, s) -> Ident(s)
    | Discrete(_, l) -> 
      let float_l = (List.map l ~f:(fun a -> Bignum.to_float(a))) in 
      (match prob with
      | None -> gen_discrete ctx float_l
      | Some(_) -> gen_discrete_sbk float_l prob)
    | Int(_, sz, v) ->
      let bits = int_to_bin sz v
                |> List.map ~f:(fun i -> if i = 1 then CG.True else CG.False) in
      mk_dfs_tuple bits
    | True(_) -> True
    | False(_) -> False
    | Observe(_, e) ->
      Observe(from_external_expr_h_sbk_e ctx cfg ann prob e)
    | Let(_, x, e1, e2) ->
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in Let(x, s1, s2)
    | Ite(_, g, thn, els) -> 
      let p, ann1, ann2, ann3 = 
        match ann with 
        | Node(ite_prob, ann1, ann2, ann3) -> 
          let p = 
            match prob with
            | None -> ite_prob
            | Some(p) -> Some(p)
          in
          p, ann1, ann2, ann3
        | Leaf -> prob, ann, ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 p g in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 p thn in
      let s3 = from_external_expr_h_sbk_e ctx cfg ann3 p els in
      Ite(s1, s2, s3)
    | Snd(_, e) -> Snd(from_external_expr_h_sbk_e ctx cfg ann prob e)
    | Fst(_, e) -> Fst(from_external_expr_h_sbk_e ctx cfg ann prob e)
    | Tup(_, e1, e2) -> 
      let ann1, ann2 = 
        match ann with 
        | Branch(ann1, ann2) -> ann1, ann2
        | Leaf -> ann, ann
        | _ -> failwith "unexpected tree element in external pass"
      in
      let s1 = from_external_expr_h_sbk_e ctx cfg ann1 prob e1 in
      let s2 = from_external_expr_h_sbk_e ctx cfg ann2 prob e2 in
      Tup(s1, s2)
    | FuncCall(src, "nth_bit", [(_, Int(_, sz, v)); e2]) ->
      if v >= sz then
        (raise (EG.Type_error (Format.sprintf "Type error at line %d column %d: nth_bit exceeds maximum bit size"
                                src.startpos.pos_lnum (get_col src.startpos))));
      let internal = from_external_expr_h_sbk_e ctx cfg ann prob e2 in
      nth_bit sz v internal
    | FuncCall(_, id, args) ->
      FuncCall(id, List.map args ~f:(fun i -> from_external_expr_h_sbk_e ctx cfg ann prob i))
    | Iter(s, f, init, k) ->
      (* let e = from_external_expr_h ctx cfg init in
      * List.fold (List.init k ~f:(fun _ -> ())) ~init:e
      *   ~f:(fun acc _ -> FuncCall(f, [acc])) *)

      let expanded = expand_iter_t s f init k in
      from_external_expr_h_sbk_e ctx cfg ann prob expanded
    | Sample(_, e) -> Sample(from_external_expr_h_sbk_e ctx cfg ann prob e)
    | IntConst(_, _) -> failwith "not implemented"
    | ListLit(_, es) -> gen_list_lit es
    | ListLitEmpty _ -> gen_list_lit []
    | Cons(s, e1, e2) ->
      gen_eval_arg e1 @@ fun x ->
        gen_eval_arg e2 @@ fun xs ->
          let length_core =
            (* if fst xs == max_list_length then max_list_length else (fst xs) + 1 *)
            let length_xs = gen_get_length xs in
            from_external_expr_h_sbk_e ctx cfg ann prob
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
        let length_core = from_external_expr_h_sbk_e ctx cfg ann prob
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
    | Length(_, e) -> Fst (from_external_expr_h_sbk_e ctx cfg ann prob e)
    | Unif(s, sz, b, e) -> 
      assert(b >= 0);
      assert(e > b);
      if b > 0 then from_external_expr_h_sbk_e ctx cfg ann prob 
        (TInt(sz), Plus(s, (TInt(sz), Int(s, sz, b)), (TInt(sz), Unif(s, sz, 0, e-b)))) else
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
        from_external_expr_h_sbk_e ctx cfg ann prob
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
      if n = 0 then from_external_expr_h_sbk_e ctx cfg ann prob intzero else 
      from_external_expr_h_sbk_e ctx cfg ann prob
        (t, Let(s, "$binomexp", (t, Ite(s, flip, intone, intzero)), make_binom_let(n-1)))   
  in
  let _, ann = annotate (t, e) in
  let e1 = from_external_expr_h_sbk_e ctx cfg ann None (t, e) in
  e1

let from_external_expr mgr cfg in_func sbk (env: EG.tenv) (e: EG.eexpr) : (EG.typ * CG.expr) =
  let ctx = if in_func then {in_func=true} else {in_func=false} in
  let (typ, e) = type_of cfg ctx env e in
  let expr = 
    if sbk then
      from_external_expr_h_sbk mgr cfg (typ, e)
    else
      from_external_expr_h mgr cfg (typ, e)
  in
  let r = (typ, expr) in
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

let from_external_func mgr cfg sbk (tenv: EG.tenv) (f: EG.func) : (EG.typ * CG.func) =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let (t, conv) = from_external_expr mgr cfg true sbk tenvwithargs f.body in
  check_return_type f t;
  (* convert arguments *)
  let args = List.map f.args ~f:(from_external_arg cfg) in
  (TFunc(List.map f.args ~f:snd, t), {name = f.name;
       args = args;
       body = conv})

let from_external_func_optimize mgr cfg sbk (tenv: EG.tenv) (f: EG.func) (local_hoisting: bool) (global_hoisting: bool) (max_flips: int option) (branch_elimination: bool) (determinism: bool) : (EG.typ * CG.func) =
  (* add the arguments to the type environment *)
  let tenvwithargs = List.fold f.args ~init:tenv ~f:(fun acc (name, typ) ->
      Map.Poly.set acc ~key:name ~data:typ
    ) in
  let (t, conv) = from_external_expr mgr cfg true sbk tenvwithargs f.body in
  check_return_type f t;
  let optbody = Optimization.do_optimize conv !n local_hoisting global_hoisting max_flips branch_elimination determinism in
  (* convert arguments *)
  let args = List.map f.args ~f:(from_external_arg cfg) in
  (TFunc(List.map f.args ~f:snd, t), {name = f.name;
        args = args;
        body = optbody})

let from_external_prog ?(cfg: config = default_config) sbk (p: EG.program) : (EG.typ * CG.program) =
  let mgr = Cudd.Man.make_d () in
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let (t, conv) = from_external_func mgr cfg sbk tenv i in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let (t, convbody) = from_external_expr mgr cfg false sbk tenv p.body in
  (t, {functions = functions; body = convbody})

let from_external_prog_optimize ?(cfg: config = default_config) sbk (p: EG.program) (local_hoisting: bool) (global_hoisting: bool) (max_flips: int option) (branch_elimination: bool) (determinism: bool) : (EG.typ * CG.program) =
  let mgr = Cudd.Man.make_d () in
  let (tenv, functions) = List.fold p.functions ~init:(Map.Poly.empty, []) ~f:(fun (tenv, flst) i ->
      let (t, conv) = from_external_func_optimize mgr cfg sbk tenv i local_hoisting global_hoisting max_flips branch_elimination determinism in
      let tenv' = Map.Poly.set tenv ~key:i.name ~data:t in
      (tenv', flst @ [conv])
    ) in
  let (t, convbody) = from_external_expr mgr cfg false sbk tenv p.body in
  let optbody = Optimization.do_optimize convbody !n local_hoisting global_hoisting max_flips branch_elimination determinism in
  (t, {functions = functions; body = optbody})

let from_core_prog (p: CG.program) : LF.program =
  let open LogicalFormula in
  let e = p.body in
  let ref_true = ref True in
  let ref_false = ref (Not(ref_true)) in

  let is_const (e: LF.expr ref) : bool =
    match !e with
    | True -> true
    | Not(e1) -> phys_equal e1 ref_true
    | Or(e1, e2) -> (phys_equal e1 ref_true) || (phys_equal e2 ref_true)
    | And(e1, e2) -> (phys_equal e1 ref_false) || (phys_equal e2 ref_false)
    | _ -> false
  in
  let is_true (e: LF.expr ref) : bool = 
    match !e with
    | True -> true
    | Or(e1, e2) -> (phys_equal e1 ref_true) || (phys_equal e2 ref_true)
    | Not(e1) -> not (phys_equal e1 ref_true)
    | And(e1, e2) -> (phys_equal e1 ref_false) || (phys_equal e2 ref_false)
    | _ -> failwith "Expression is not a constant"
  in
  let weights = Hashtbl.Poly.create () in
  let env = Hashtbl.Poly.create () in

  let binary = Hashtbl.Poly.create () in
  let unary = Hashtbl.Poly.create () in

  let binary_ref = ref binary in
  let unary_ref = ref unary in

  let rec from_core_prog_h (e: CG.expr) : LF.expr ref = 
    match e with
    | And(e1, e2) -> 
      let c1 = from_core_prog_h e1 in
      let c2 = from_core_prog_h e2 in
      let ref_node = Hashtbl.Poly.find_or_add binary (c1, c2, And_ind) 
        ~default:(fun () -> ref (And(c1, c2))) in
      ref_node
    | Or(e1, e2) -> 
      let c1 = from_core_prog_h e1 in
      let c2 = from_core_prog_h e2 in
      let ref_node = Hashtbl.Poly.find_or_add binary (c1, c2, Or_ind) 
        ~default:(fun () -> ref (Or(c1, c2))) in
      ref_node
    | Xor(e1, e2) -> 
      let c1 = from_core_prog_h e1 in
      let c2 = from_core_prog_h e2 in
      let ref_not_c1 = Hashtbl.Poly.find_or_add unary c1
        ~default:(fun () -> ref (Not(c1))) in
      let ref_not_c2 = Hashtbl.Poly.find_or_add unary c2
        ~default:(fun () -> ref (Not(c2))) in
      let ref_and1 = Hashtbl.Poly.find_or_add binary (c1, ref_not_c2, And_ind)
        ~default:(fun () -> ref (And(c1, ref_not_c2))) in
      let ref_and2 = Hashtbl.Poly.find_or_add binary (ref_not_c1, c2, And_ind)
        ~default:(fun () -> ref (And(ref_not_c1, c2))) in
      let ref_or = Hashtbl.Poly.find_or_add binary (ref_and1, ref_and2, Or_ind)
        ~default:(fun () -> ref (Or(ref_and1, ref_and2))) in
      ref_or
    | Eq(e1, e2) -> 
      let c1 = from_core_prog_h e1 in
      let c2 = from_core_prog_h e2 in
      let ref_not_c1 = Hashtbl.Poly.find_or_add unary c1
        ~default:(fun () -> ref (Not(c1))) in
      let ref_not_c2 = Hashtbl.Poly.find_or_add unary c2
        ~default:(fun () -> ref (Not(c2))) in
      let ref_or1 = Hashtbl.Poly.find_or_add binary (ref_not_c1, c2, Or_ind)
        ~default:(fun () -> ref (Or(ref_not_c1, c2))) in
      let ref_or2 = Hashtbl.Poly.find_or_add binary (c1, ref_not_c2, Or_ind)
        ~default:(fun () -> ref (Or(c1, ref_not_c2))) in
      let ref_and = Hashtbl.Poly.find_or_add binary (ref_or1, ref_or2, And_ind)
        ~default:(fun () -> ref (And(ref_or1, ref_or2))) in
      ref_and
      (* Or(And(c1, c2), And(Not(c1), Not(c2))) *)
    | Not(e) ->
      let c = from_core_prog_h e in
      let ref_not_c = Hashtbl.Poly.find_or_add unary c
        ~default:(fun () -> ref (Not(c))) in
      ref_not_c
    | True -> ref_true
    | False -> ref_false
    | Ident(s) ->
      (match Hashtbl.Poly.find env s with
      | Some(r) -> r
      | _ -> failwith (sprintf "Could not find variable '%s'" s))
    | Tup(e1, e2) ->
      let c1 = from_core_prog_h e1 in
      let c2 = from_core_prog_h e2 in
      let ref_node = Hashtbl.Poly.find_or_add binary (c1, c2, Tup_ind)
        ~default:(fun () -> ref (Tup(c1, c2))) in
      ref_node
    | Ite(g, thn, els) ->
      let cg = from_core_prog_h g in
      if is_const cg then
        let r = from_core_prog_h (if is_true cg then thn else els) in
        r
      else
        let cthn = from_core_prog_h thn in
        let cels = from_core_prog_h els in
        let ref_not_cg = Hashtbl.Poly.find_or_add unary cg
          ~default:(fun () -> ref (Not(cg))) in
        let ref_and1 = Hashtbl.Poly.find_or_add binary (cg, cthn, And_ind)
          ~default:(fun () -> ref (And(cg, cthn))) in
        let ref_and2 = Hashtbl.Poly.find_or_add binary (ref_not_cg, cels, And_ind)
          ~default:(fun () -> ref (And(ref_not_cg, cels))) in
        let ref_or = Hashtbl.Poly.find_or_add binary (ref_and1, ref_and2, Or_ind)
          ~default:(fun () -> ref (Or(ref_and1, ref_and2))) in
        ref_or
    | Fst(e) ->
      let c = from_core_prog_h e in
      let r = match !(LF.extract_tup c (ref binary)) with
      | Tup(c1, _) -> c1
      | _ -> failwith (Format.sprintf "Internal Failure: calling `fst` on non-tuple at %s" (LF.string_of_expr c))
      in 
      r
    | Snd(e) ->
      let c = from_core_prog_h e in
      let r = match !(LF.extract_tup c (ref binary)) with
      | Tup(_, c2) -> c2
      | _ -> failwith (Format.sprintf "Internal Failure: calling `snd` on non-tuple at %s" (CG.string_of_expr e))
      in 
      r
    | Flip(f) ->
      let var_name = (Format.sprintf "f%d_%s" !flip_id (Bignum.to_string_hum f)) in
      flip_id := !flip_id + 1;
      (if Bignum.equal f Bignum.one then () else Hashtbl.Poly.add_exn weights ~key:var_name ~data:f);
      ref (Atom(var_name))
    | Observe(g) ->
      let c = from_core_prog_h g in
      c
    | Let(x, e1, e2) ->
      let c1 = from_core_prog_h e1 in
      let c2 = Hashtbl.Poly.find_and_call env x ~if_found:(fun data ->
        (Hashtbl.Poly.set env ~key:x ~data:c1);
        let c2 = from_core_prog_h e2 in
        (Hashtbl.Poly.set env ~key:x ~data:data);
        c2
        ) ~if_not_found:(fun x ->
          (Hashtbl.Poly.set env ~key:x ~data:c1);
          let c2 = from_core_prog_h e2 in
          (Hashtbl.Poly.remove env x);
          c2
        )
      in
      c2
    | Sample(_) -> failwith "not implemented"
    | FuncCall(_, _) -> failwith "not implemented"
    | _ -> failwith "not implemented"
  in

  let rec remove_redundancy (e: LF.expr ref) : LF.expr ref =
    match !e with 
    | And(e1, e2) -> 
      let e1' = remove_redundancy e1 in
      let e2' = remove_redundancy e2 in
      if phys_equal e1' ref_true then
        e2'
      else if phys_equal e2' ref_true then
          e1'
      else if phys_equal e1' ref_false || phys_equal e2' ref_false then
          ref_false
      else
        let ref_node = Hashtbl.Poly.find_or_add binary (e1', e2', And_ind)
          ~default:(fun () -> ref (And(e1', e2'))) in
        ref_node
    | Or(e1, e2) -> 
      let e1' = remove_redundancy e1 in
      let e2' = remove_redundancy e2 in
      if phys_equal e1' ref_true || phys_equal e2' ref_true then
        ref_true
      else if phys_equal e1' ref_false then
        e2'
      else if phys_equal e2' ref_false then
        e1'
      else
        let ref_node = Hashtbl.Poly.find_or_add binary (e1', e2', Or_ind)
          ~default:(fun () -> ref (Or(e1', e2'))) in
        ref_node
    | Atom(_) -> e
    | True -> ref_true
    | Not(e1) -> 
      let e1' = remove_redundancy e1 in
      (match !e1' with
      | Not(e2) -> e2
      | _ -> 
        let ref_not = Hashtbl.Poly.find_or_add unary e1'
          ~default:(fun () -> ref (Not(e1'))) in
        ref_not)
    | Tup(e1, e2) -> 
      let e1' = remove_redundancy e1 in
      let e2' = remove_redundancy e2 in
      let ref_node = Hashtbl.Poly.find_or_add binary (e1', e2', Tup_ind)
        ~default:(fun () -> ref (Tup(e1', e2'))) in
      ref_node
  in

  let r = from_core_prog_h e in
  let r = remove_redundancy r in
  {body = r; weights = weights; binary = binary_ref; unary = unary_ref;}

(* Assumes the Bayesian Network format *)
let select_marginals ?(partial = 0) (random: bool) (p: EG.program) : EG.program =
  let rec get_roots (e: EG.eexpr) : EG.eexpr =
    match e with
    | Let(_,_,_,e2) -> get_roots e2
    | Tup(_) | Ident(_) -> e
    | _ -> failwith "Not implemented"
  in

  let length (e: EG.eexpr) : int = 
    let rec length_e (e: EG.eexpr) (acc: int) : int =
      match e with
      | Tup(_, Ident(_, x), e2) ->
        Format.printf "%s " x;
        length_e e2 (acc + 1)
      | Tup(_, e1, e2) ->
        let s1 = length_e e1 acc in
        length_e e2 s1
      | Ident(_, x) ->
        Format.printf "%s " x;
        acc + 1
      | _ -> failwith "Not implemented1"
    in
    length_e e 0
  in

  let extract (e: EG.eexpr) (idx: int list) : EG.eexpr = 
    let idx = List.sort idx ~compare: Poly.compare in
    let rec extract_e (e: EG.eexpr) (idx: int list) (i: int) (acc: EG.eexpr option) : EG.eexpr option = 
      let open ExternalGrammar in
      match idx with
      | [] -> acc
      | head::tail ->
        if head = i then
          (match e with
          | Tup(s, Ident(sx,x), e2) ->
            let acc' = match acc with
            | None -> Ident(sx, x)
            | Some(acc) -> Tup(s, Ident(sx, x), acc)
            in
            extract_e e2 tail (i + 1) (Some(acc'))
          | Ident(s, x) ->
            let acc' = match acc with
            | None -> Ident(s, x)
            | Some(acc) -> Tup(s, Ident(s, x), acc)
            in
            Some(acc')
          | _ -> failwith "Not implemented")
        else
          (match e with
          | Tup(_, Ident(_), e2) ->
            extract_e e2 idx (i + 1) acc
          | Ident(_) ->
            acc
          | _ -> failwith "Not implemented")
    in
    match extract_e e idx 0 None with
    | None -> failwith "Failed to extract marginals"
    | Some(e) -> e
  in

  if random then
    (* take random marginal *)
    let e = p.body in
    let roots = get_roots e in
    
    let n = length roots in 
    if n < 2 then
      p
    else
      let x = Random.int n in
      let new_root = extract roots [x] in

      let e' = 
        let open ExternalGrammar in
        match e with
        | Let(s, x, e1, _) -> Let(s, x, e1, new_root)
        | _ -> failwith "Not implemented"
      in
      {body=e'; functions=p.functions}
  else
    if partial = 0 then
      (* take half *)
      p
    else
      (* take partial marginals *)
      p
