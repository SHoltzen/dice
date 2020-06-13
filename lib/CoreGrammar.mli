(** Defines the core internal dice grammar *)

type expr =
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Ident of String.t
  | Fst of expr
  | Snd of expr
  | Tup of expr * expr
  | Ite of expr * expr * expr
  | Discrete of float List.t
  | Eq of expr * expr
  | Lt of expr * expr
  | Int of int * int  (* sz, v *)
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Div of expr * expr
  | True
  | False
  | Flip of float
  | Let of String.t * expr * expr
  | FuncCall of String.t * expr List.t
  | Observe of expr
[@@deriving sexp_of]
and fcall = {
  fname: String.t;
  args: expr
}
[@@deriving sexp_of]

val string_of_expr : expr -> String.t

type typ =
    TBool
  | TInt of int (* sz *)
  | TTuple of typ * typ
[@@deriving sexp_of]

(** A function argument *)
type arg = String.t * typ
[@@deriving sexp_of]

(** Core function *)
type func = {
  name: String.t;
  args: arg List.t;
  body: expr;
}
[@@deriving sexp_of]

(** Core program *)
type program = {
  functions: func List.t;
  body: expr;
}
[@@deriving sexp_of]


(** type environment *)
type tenv = (String.t, typ) Core.Map.Poly.t

val type_of : tenv -> expr -> typ
val type_of_fun : tenv -> func -> typ
