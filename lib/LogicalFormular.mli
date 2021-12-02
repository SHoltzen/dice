(** Defines the logical formula interface in dice grammar *)

type LogicalFormula =
    | And of LogicalFormula * LogicalFormula
    | Or of LogicalFormula * LogicalFormula
    | Atom of String.t
    | Neg of LogicalFormula
[@@deriving sexp_of]

type Literal = 
    | Pos of String.t
    | Neg of String.t
[@@deriving sexp_of]

type Cnf = List.t of List.t of Literal
[@@deriving sexp_of]

type Dddnf = List.t of List.t of Literal
[@@deriving sexp_of]

val compile_to_bdd : LogicalFormula -> bddptr
val compile_to_cnf : LogicalFormula -> Cnf (* tseytin encoding *)
val compile_cnf_to_ddnf : Cnf -> Dddnf (* calls sharpsat *)