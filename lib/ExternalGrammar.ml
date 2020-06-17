(**
   Public-facing grammar. This is the parser target.
*)

open Core
open Sexplib.Std

type typ =
    TBool
  | TInt of int (* sz *)
  | TTuple of typ * typ
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
  | True of source
  | False of source
[@@deriving sexp_of]

type func = { name: String.t; args: arg List.t; body: eexpr}
[@@deriving sexp_of]

type program = { functions: func List.t; body: eexpr }
[@@deriving sexp_of]



exception Type_error of String.t

let rec traverse f e =
  match e with
  | And(s, e1, e2) ->
    let s1 = traverse f e1 in
    let s2 = traverse f e2 in f (And(s, s1, s2))
  | Or(s, e1, e2) ->
    let s1 = traverse f e1 in
    let s2 = traverse f e2 in f (Or(s, s1, s2))
  | Iff(s, e1, e2) ->
    let s1 = traverse f e1 in
    let s2 = traverse f e2 in f (Iff(s, s1, s2))
  | Plus(s, e1, e2) -> f (Plus(s, traverse  f  e1, traverse  f  e2))
  | Eq(s, e1, e2) -> f (Eq(s, traverse  f  e1, traverse  f  e2))
  | Neq(s, e1, e2) -> f (Neq(s, traverse  f  e1, traverse  f  e2))
  | Minus(s, e1, e2) -> f (Minus(s, traverse f e1, traverse f e2))
  | Mult(s, e1, e2) -> f (Mult(s, traverse f e1, traverse f e2))
  | Div(s, e1, e2) -> f (Div(s, traverse  f  e1, traverse  f  e2))
  | Lt(s, e1, e2) -> f (Lt(s, traverse  f  e1, traverse  f  e2))
  | Lte(s, e1, e2) -> traverse f (Or(s, Lt(s, e1, e2), Eq(s, e1, e2)))
  | Gt(s, e1, e2) -> traverse f (Not(s, Lte(s, e1, e2)))
  | Gte(s, e1, e2) -> traverse f (Not(s, Lt(s, e1, e2)))
  | Not(s, e) -> f (Not(s, traverse  f  e))
  | IntConst(_, _)
  | Flip(_, _)
  | Ident(_, _)
  | Discrete(_, _)
  | Int(_, _, _)
  | True(_)
  | False(_) -> f e
  | Observe(s, g) -> f (Observe(s, traverse f g))
  | Let(s, x, e1, e2) -> f (Let(s, x, traverse  f  e1, traverse f e2))
  | Ite(s, g, thn, els) -> f (Ite(s, traverse f g, traverse f thn, traverse f els))
  | Snd(s, e) -> f (Snd(s, traverse f e))
  | Fst(s, e) -> f (Fst(s, traverse f e))
  | Tup(s, e1, e2) -> f (Tup(s, traverse f e1, traverse f e2))
  | Iter(s, func, init, k) ->
    f (Iter(s, func, traverse f init, k))
  | FuncCall(s, id, args) -> f (FuncCall(s, id, (List.map args ~f:f)))


let get_src e =
  match e with
  | And(s, _, _)
  | Or(s, _, _)
  | Plus(s, _, _)
  | Eq(s, _, _)
  | Neq(s, _, _)
  | Minus(s, _, _)
  | Mult(s, _, _)
  | Div(s, _, _)
  | Lt(s, _, _)
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
  | FuncCall(s, _, _) -> s



let string_of_eexpr e =
  Sexp.to_string_hum (sexp_of_eexpr e)

let string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)

let string_of_typ t =
  Sexp.to_string_hum (sexp_of_typ t)

(** type environment *)
type tenv = (String.t, typ) Core.Map.Poly.t
