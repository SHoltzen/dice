(**
   Public-facing grammar. This is the parser target.
*)

open Core
open Sexplib.Std
open Bignum

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
  | Flip of source * Bignum.t
  | Let of source * String.t * eexpr * eexpr
  | Observe of source * eexpr
  | Ident of source * String.t
  | Discrete of source * Bignum.t List.t
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
  | Binom of source * int * int * Bignum.t
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
