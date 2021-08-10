open Core

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


type arg = String.t * typ
[@@deriving sexp_of]

let string_of_expr e =
  Sexp.to_string_hum (sexp_of_expr e)

type tenv = (String.t, typ) Map.Poly.t

let rec type_of env e : typ =
  match e with
  | And(_, _) | Xor(_, _) | Eq(_, _) | Or(_, _) | Not(_) | True | False | Flip(_) | Observe(_) -> TBool
  | Ident(s) -> (try Map.Poly.find_exn env s
    with _ -> failwith (Format.sprintf "Could not find variable %s during typechecking" s))
  | Sample(e) -> type_of env e
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

let string_of_prog_unparsed p =
  let body = p.body in
  let functions = p.functions in 

  let string_of_op e = 
    match e with 
    | And(_, _) -> "&&"
    | Xor(_, _) -> "^"
    | Eq(_, _) -> "=="
    | Or(_, _) -> "||"
    | Observe(_) -> "observe"
    | Fst(_) -> "fst"
    | Snd(_) -> "snd"
    | Sample(_) -> "sample"
    | _ -> ""
  in

  let rec pr_func e = 
    Format.dprintf "@[<hov 2>%t@]" (pr_expr e)
  and string_of_type typ = 
    match typ with
    | TBool -> "bool"
    | TTuple(t1, t2) -> Format.asprintf "(%s, %s)" (string_of_type t1) (string_of_type t2)
  and
  pr_expr e = 
    match e with
    | Let(x, e1, e2) ->
      let s1 = pr_expr e1 in
      let s2 = pr_expr e2 in
      Format.dprintf "@[<hv>@[let@ %s@ =@;<1 2>%t@;in@]@\n%t@]" x s1 s2
    | Ite(g, thn, els) ->
      let s0 = pr_expr g in
      let s1 = pr_expr thn in
      let s2 = pr_expr els in
      Format.dprintf "@[<hv>@[if@;<1 2>%t@;then@]@;<1 2>@[%t@]@;else@;<1 2>@[%t@]@]" s0 s1 s2
    | And(e1, e2) | Xor(e1, e2) | Eq(e1, e2) | Or(e1, e2) -> 
      let s1 = pr_expr e1 in
      let s2 = pr_expr e2 in
      Format.dprintf "@[<hov 2>%t@ %s@;%t@]" s1 (string_of_op e) s2
    | Tup(e1, e2) ->
      let s1 = pr_expr e1 in
      let s2 = pr_expr e2 in
      Format.dprintf "@[<hov 2>(%t,@ %t)@]" s1 s2
    | Not(e1) -> 
      let s1 = pr_expr e1 in
      Format.dprintf "!%t" s1
    | Observe(e1) | Fst(e1) | Snd(e1) | Sample(e1) ->
      let s1 = pr_expr e1 in
      Format.dprintf "@[<hov 2>%s@ %t@]" (string_of_op e) s1
    | Flip(f) -> Format.dprintf "flip %s" (Bignum.to_string_hum f)
    | Ident(s) -> Format.dprintf "%s" s
    | FuncCall(id, args) ->
      let args_s = 
        match args with
        | [] -> Format.dprintf ""
        | head::[] -> Format.dprintf "%t" (pr_expr head)
        | head::tail -> 
          List.fold tail ~init:(Format.dprintf "%t" (pr_expr head)) ~f:(fun prev arg -> Format.dprintf "%t,@ %t" prev (pr_expr arg))
      in
      Format.dprintf "@[<hov 2>%s(%t)@]" id args_s
    | True -> Format.dprintf "true"
    | False -> Format.dprintf "false"
  in 
  
  let string_of_functions = List.fold functions ~init:(Format.dprintf "") ~f:(fun prev func -> 
    let string_of_args = 
      match func.args with
        | [] -> Format.dprintf ""
        | (var, typ)::[] -> Format.dprintf "%s: %s" var (string_of_type typ)
        | (var, typ)::tail -> 
          List.fold tail ~init:(Format.dprintf "%s: %s" var (string_of_type typ)) ~f:(fun prev (var, typ) -> Format.dprintf "%t,@ %t" prev (Format.dprintf "%s: %s" var (string_of_type typ)))
    in
    Format.dprintf "@[%t\n@[fun@ %s(%t)@]@\n@<100>{@;<1 2>%t@;}@]\n" prev func.name string_of_args (pr_func func.body)
  ) in
  Format.asprintf "%s%s" (Format.asprintf "%t\n" string_of_functions) (Format.asprintf "%t\n" (pr_func body))