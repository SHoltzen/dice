(**
   Public-facing grammar. This is the parser target.
*)

open Core
open Sexplib.Std


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
  | Fst of eexpr
  | Snd of eexpr
  | Tup of eexpr * eexpr
  | True
  | False
[@@deriving sexp]

let rec string_of_eexpr e =
  match e with
  | And(e1, e2) -> sprintf "%s && %s" (string_of_eexpr e1) (string_of_eexpr e2)
  | Or(e1, e2) -> sprintf "%s || %s" (string_of_eexpr e1) (string_of_eexpr e2)
  | Eq(e1, e2) -> sprintf "%s == %s" (string_of_eexpr e1) (string_of_eexpr e2)
  | Plus(e1, e2) -> sprintf "%s + %s" (string_of_eexpr e1) (string_of_eexpr e2)
  | Not(e) -> sprintf "! %s" (string_of_eexpr e)
  | Ite(g, thn, els) ->
    sprintf "if %s then %s else %s"
      (string_of_eexpr g) (string_of_eexpr thn) (string_of_eexpr els)
  | Let(id, e1, e2) ->
    sprintf "let %s = %s in %s"
      id (string_of_eexpr e1) (string_of_eexpr e2)
  | Observe(e) -> sprintf "observe %s" (string_of_eexpr e)
  | True -> "true"
  | False -> "false"
  | Flip(f) -> sprintf "flip %f" f
  | Ident(s) -> s
  | Snd(e) -> sprintf "snd %s" (string_of_eexpr e)
  | Fst(e) -> sprintf "fst %s" (string_of_eexpr e)
  | Tup(e1, e2) -> sprintf "(%s, %s)" (string_of_eexpr e1) (string_of_eexpr e2)
  | Discrete(l) ->
    sprintf "Discrete(%s)" (List.to_string ~f:string_of_float l)
  | Int(sz, value) -> sprintf "Int(%d, %d)" sz value
