(**
   Public-facing grammar. This is the parser target.
*)

open Core
open Sexplib.Std

type typ =
    TBool
  | TInt of int (* sz *)
  | TTuple of typ * typ
  | TList of typ
  | TFunc of typ List.t * typ
[@@deriving sexp_of]

type arg = String.t * typ
[@@deriving sexp_of]

(* this syntax is a bit weird; it is necessary because Lexing.position does not
   by default derive sexp. *)
type lexing_position =
  Lexing.position =
  { pos_fname : string
  ; pos_lnum : int
  ; pos_bol : int
  ; pos_cnum : int
  }
[@@deriving sexp]


type source = {startpos: lexing_position; endpos: lexing_position}
[@@deriving sexp_of]

type eexpr =
    And of source * eexpr * eexpr
  | Or of source * eexpr * eexpr
  | Iff of source * eexpr * eexpr
  | Xor of source * eexpr * eexpr
  | Sample of source * eexpr
  | IntConst of source * int
  | Not of source * eexpr
  | Ite of source * eexpr * eexpr * eexpr
  | Flip of source * float
  | Let of source * String.t * eexpr * eexpr
  | Observe of source * eexpr
  | Ident of source * String.t
  | Discrete of source * float List.t
  | Int of source * int * int (* value, size *)
  | Eq of source * eexpr * eexpr
  | LeftShift of source * eexpr * int
  | RightShift of source * eexpr * int
  | Plus of source * eexpr * eexpr
  | Minus of source * eexpr * eexpr
  | Mult of source * eexpr * eexpr
  | Div of source * eexpr * eexpr
  | Lte of source * eexpr * eexpr
  | Lt of source * eexpr * eexpr
  | Gte of source * eexpr * eexpr
  | Gt of source * eexpr * eexpr
  | Neq of source * eexpr * eexpr
  | Fst of source * eexpr
  | Snd of source * eexpr
  | Tup of source * eexpr * eexpr
  | FuncCall of source * String.t * eexpr List.t
  | Iter of source * String.t * eexpr * int
  | Unif of source * int * int * int 
  | Binom of source * int * int * float
  | True of source
  | False of source
  | ListLit of source * eexpr List.t
  | ListLitEmpty of source * typ
  | Cons of source * eexpr * eexpr
  | Head of source * eexpr
  | Tail of source * eexpr
  | Length of source * eexpr
[@@deriving sexp_of]

type func = { name: String.t; args: arg List.t; return_type: typ option; body: eexpr}
[@@deriving sexp_of]

type program = { functions: func List.t; body: eexpr }
[@@deriving sexp_of]



exception Type_error of String.t

let get_src e =
  match e with
  | And(s, _, _)
  | Or(s, _, _)
  | Xor(s, _, _)
  | Plus(s, _, _)
  | Eq(s, _, _)
  | Neq(s, _, _)
  | Minus(s, _, _)
  | Mult(s, _, _)
  | Div(s, _, _)
  | Lt(s, _, _)
  | Sample(s, _)
  | Lte(s, _, _)
  | Gt(s, _, _)
  | Int(s, _, _)
  | Iff(s, _, _)
  | Gte(s, _, _) -> s
  | IntConst(s, _) -> s
  | Not(s, _) -> s
  | Flip(s, _) -> s
  | Ident(s, _) -> s
  | Discrete(s, _) -> s
  | True(s) -> s
  | False(s) -> s
  | Observe(s, _) -> s
  | Let(s, _, _, _) -> s
  | Ite(s, _, _, _) -> s
  | Snd(s, _) -> s
  | Fst(s, _) -> s
  | Tup(s, _, _) -> s
  | Iter(s, _, _, _) -> s
  | Unif(s, _, _, _) -> s
  | Binom(s, _, _, _) -> s
  | FuncCall(s, _, _) -> s
  | LeftShift(s, _, _) -> s
  | RightShift(s, _, _) -> s
  | ListLit(s, _) -> s
  | ListLitEmpty(s, _) -> s
  | Cons(s, _, _) -> s
  | Head(s, _) -> s
  | Tail(s, _) -> s
  | Length(s, _) -> s

let gen_src =
  let gen_pos = { Lexing.dummy_pos with pos_fname = "<generated>" } in
  { startpos = gen_pos; endpos = gen_pos }

let string_of_eexpr e =
  Sexp.to_string_hum (sexp_of_eexpr e)

let string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)

let string_of_typ t =
  Sexp.to_string_hum (sexp_of_typ t)

(** type environment *)
type tenv = (String.t, typ) Core.Map.Poly.t

let count_params p = 
  let funcs = p.functions in
  let e = p.body in
  let round_float x =
    let d = 6 in
    let m = 10. ** (float d) in 
    (Float.round_down ((x *. m) +. 0.5)) /. m
  in
  let equal f1 f2 = Float.equal (round_float f1) (round_float f2) in
  let rec count_params_e e c s params =
    match e with
    | Let(_, _, e1, e2) ->
      let c1, s1, _ = count_params_e e1 c s [] in
      count_params_e e2 c1 s1 []
    | And(_, e1, e2) | Or(_, e1, e2) | Iff(_, e1, e2) | Xor(_, e1, e2) 
    | Plus(_, e1, e2) | Minus(_, e1, e2) | Eq(_, e1, e2) | Neq(_, e1, e2) 
    | Mult(_, e1, e2) | Lt(_, e1, e2) | Lte(_, e1, e2) | Gt(_, e1, e2)
    | Gte(_, e1, e2) | Tup(_, e1, e2) | Cons(_, e1, e2) 
    | Div(_, e1, e2) ->
      let c1, s1, p1 = count_params_e e1 c s params in
      count_params_e e2 c1 s1 p1
    | Not(_, e1) | LeftShift(_, e1, _) | RightShift(_, e1, _) | Observe(_, e1) 
    | Snd(_, e1) | Fst(_, e1) | Sample(_, e1) | Length(_, e1) | Iter(_, _, e1, _) 
    | Head(_, e1) | Tail(_, e1) ->
      count_params_e e1 c s params
    | Flip(_, f) -> 
      let s1 = 
        if equal f 1.0 or equal f 0.0 then
          s 
        else 
          s + 1 
      in
      if List.mem params f ~equal: equal then c, s1, params else (c + 1), s1, f::params
    | Discrete(_, l) -> 
      List.fold l ~init: (c, s, params) ~f: (fun (c, s, p) a -> 
        let s1 =
          if equal a 1.0 or equal a 0.0 then
            s
          else 
            s + 1
        in
        if List.mem p a ~equal: equal then (c, s1, p) else (c + 1, s1, a::p))
    | Ident(_, _) | Int(_, _, _) | True(_) | False(_) | IntConst(_, _) 
    | ListLitEmpty _ | Unif (_, _, _, _) | Binom (_, _, _, _) -> c, s, params
    | ListLit(_, es) | FuncCall(_, _, es) ->
      List.fold es ~init: (c, s, params) ~f: (fun (c, s, params) e1 -> count_params_e e1 c s params)
    | Ite(_, g, thn, els) -> 
      let c1, s1, p1 = count_params_e g c s params in
      let c2, s2, p2 = count_params_e thn c1 s1 p1 in
      count_params_e els c2 s2 p2
  in

  let c, s, _ = List.fold funcs ~init: (0, 0, []) ~f: (fun (c, s, params) f -> 
    count_params_e f.body c s params) in
  let c1, s1, _ = count_params_e e c s [] in
  
  (Format.sprintf "%d\n" c1), (Format.sprintf "%d\n" s1)