type manager
type bddptr
type label

val mk_bdd_manager_default_order : int -> manager
val bdd_newvar : manager -> bool -> bddptr
val bdd_and : manager -> bddptr -> bddptr -> bddptr
val bdd_ite : manager -> bddptr -> bddptr -> bddptr -> bddptr
val bdd_or : manager -> bddptr -> bddptr -> bddptr
val bdd_negate : manager -> bddptr -> bddptr
val bdd_iff : manager -> bddptr -> bddptr -> bddptr
val bdd_xor : manager -> bddptr -> bddptr -> bddptr
val bdd_is_true : manager -> bddptr -> bool
val bdd_is_false : manager -> bddptr -> bool
val bdd_true : manager -> bddptr
val bdd_false : manager -> bddptr
val bdd_exists : manager -> bddptr -> label -> bddptr
val bdd_condition : manager -> bddptr -> label -> bool -> bddptr
val bdd_compose : manager -> bddptr -> label -> bddptr -> bddptr
val bdd_vector_compose : manager -> bddptr -> label List.t -> bddptr List.t -> bddptr
val bdd_size : manager -> bddptr -> Unsigned.uint64
val bdd_topvar : manager -> bddptr -> label
val bdd_is_var : manager -> bddptr -> bool
val bdd_is_const : manager -> bddptr -> bool
val bdd_eq : manager -> bddptr -> bddptr -> bool
val bdd_low : manager -> bddptr -> bddptr
val bdd_high : manager -> bddptr -> bddptr
val man_print_stats : manager -> unit
val bdd_num_recursive_calls : manager -> Unsigned.uint64
val int_of_label : label -> int
