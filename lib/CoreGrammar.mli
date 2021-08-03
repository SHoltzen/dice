(** Defines the core internal dice grammar *)



type expr =
  | And of expr * expr
  | Or of expr * expr
  | Eq of expr * expr
  | Xor of expr * expr
  | Not of expr
  | Ident of String.t
  | Sample of expr
  | Fst of expr
  | Snd of expr
  | Tup of expr * expr
  | Ite of expr * expr * expr
  | True
  | False
  | Flip of Bignum.t
  | Let of String.t * expr * expr
  | FuncCall of String.t * expr List.t
  | Observe of expr
[@@deriving sexp_of]
and fcall = {
  fname: String.t;
  args: expr
}
[@@deriving sexp_of]


type typ =
    TBool
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

val string_of_expr : expr -> String.t
val string_of_prog : program -> String.t
val string_of_prog_unparsed : program -> String.t