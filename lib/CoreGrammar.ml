open Core

type binop =
  | And
  | Or
  | Eq
  | Xor
[@@deriving sexp_of]

type expr =
  | Binop of binop * expr * expr
  | Not of expr
  | Ident of String.t
  | Fst of expr
  | Snd of expr
  | Tup of expr * expr
  | Ite of expr * expr * expr
  | Flip of float
  | Let of String.t * expr * expr
  | FuncCall of String.t * expr List.t
  | Observe of expr
  | DeltaB of bool pureexpr
and _ pureexpr =
  | PTrue : bool pureexpr
  | PFalse : bool pureexpr
  | POr : (bool -> bool -> bool) pureexpr
  | PAnd : (bool -> bool -> bool) pureexpr
  | PEq : (bool -> bool -> bool) pureexpr
  | PSample : (expr -> bool) pureexpr
  (* | PFalse
   * | PAnd of expr * expr
   * | POr of expr * expr
   * | PEq of expr * expr
   * | PXor of expr * expr
   * | PNot of expr
   * | PIdent of String.t
   * | PSample of expr
   * | PFst of expr
   * | PSnd of expr
   * | PTup of expr * expr
   * | PIte of expr * expr * expr
   * | PLet of String.t * expr * expr
   * | PFuncCall of String.t * expr List.t *)

let sexp_of_pureexpr e = failwith "not implemented"
let sexp_of_expr e = failwith "not implemented"

type fcall = {
  fname: String.t;
  args: expr
}
[@@deriving sexp_of]

type typ =
    TBool
  | TTuple of typ * typ
[@@deriving sexp_of]

type arg = String.t * typ
[@@deriving sexp_of]

let string_of_expr e =
  Sexp.to_string_hum (sexp_of_expr e)

type tenv = (String.t, typ) Map.Poly.t

let rec type_of env e : typ =
  match e with
  | DeltaB(_) | Binop(_, _, _) | Not(_) | Flip(_) | Observe(_) -> TBool
  | Ident(s) -> (try Map.Poly.find_exn env s
    with _ -> failwith (Format.sprintf "Could not find variable %s during typechecking" s))
  (* | BinopPI(_, e1, _) -> type_of env e1 *)
  | Fst(e1) ->
    (match type_of env e1 with
     | TTuple(l, _) -> l
     | _ -> failwith "Type error: expected tuple")
  | Snd(e1) ->
    (match type_of env e1 with
     | TTuple(_, r) -> r
     | _ -> failwith "Type error: expected tuple")
  | Tup(e1, e2) ->
    let t1 = type_of env e1 in
    let t2 = type_of env e2 in
    TTuple(t1 ,t2)
  | Let(x, e1, e2) ->
    let te1 = type_of env e1 in
    type_of (Map.Poly.set env ~key:x ~data:te1) e2
  | Ite(_, thn, _) ->
    let t1 = type_of env thn in
    (* let t2 = type_of env els in *)
    (* assert (t1 == t2); *)
    t1
  | FuncCall(id, _) ->
    (try Map.Poly.find_exn env id
    with _ -> failwith (Format.sprintf "Could not find function '%s' during typechecking" id))


(** Core function grammar *)
type func = {
  name: String.t;
  args: arg List.t;
  body: expr;
}
[@@deriving sexp_of]

let type_of_fun env f : typ =
  (* set up the type environment and then type the body *)
  let new_env = List.fold ~init:env f.args ~f:(fun acc (name, typ) ->
      Map.Poly.add_exn acc ~key:name ~data:typ
    ) in
  type_of new_env f.body

type program = {
  functions: func List.t;
  body: expr;
}
[@@deriving sexp_of]

let string_of_prog e =
  Sexp.to_string_hum (sexp_of_program e)

