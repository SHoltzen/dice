(**
   Public-facing grammar. This is the parser target.
*)

open Core
open Sexplib.Std

type typ =
    TBool
  | TInt of int (* sz *)
  | TTuple of typ * typ
[@@deriving sexp_of]

type arg = String.t * typ
[@@deriving sexp_of]

type eexpr =
    And of eexpr * eexpr
  | Or of eexpr * eexpr
  | Not of eexpr
  | Ite of eexpr * eexpr * eexpr
  | Flip of float
  | Let of String.t * eexpr * eexpr
  | Observe of eexpr
  | Ident of String.t
  | Discrete of float List.t
  | Int of int * int (* value, size *)
  | Eq of eexpr * eexpr
  | Plus of eexpr * eexpr
  | Minus of eexpr * eexpr
  | Mult of eexpr * eexpr
  | Div of eexpr * eexpr
  | Lte of eexpr * eexpr
  | Lt of eexpr * eexpr
  | Gte of eexpr * eexpr
  | Gt of eexpr * eexpr
  | Neq of eexpr * eexpr
  | Fst of eexpr
  | Snd of eexpr
  | Tup of eexpr * eexpr
  | FuncCall of String.t * eexpr List.t
  | Iter of String.t * eexpr * int
  | True
  | False
[@@deriving sexp_of]

type func = { name: String.t; args: arg List.t; body: eexpr}
[@@deriving sexp_of]

type program = { functions: func List.t; body: eexpr }
[@@deriving sexp_of]

let rec string_of_eexpr e =
  Sexp.to_string_hum (sexp_of_eexpr e)

let rec string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)
