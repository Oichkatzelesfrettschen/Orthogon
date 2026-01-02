
val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val sub : int -> int -> int

  val max : int -> int -> int

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val nth_error : 'a1 list -> int -> 'a1 option

val concat : 'a1 list list -> 'a1 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val mul : int -> int -> int

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lxor : int -> int -> int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val succ_pos : int -> int

  val coq_lxor : int -> int -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val eqb : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int

  val of_N : int -> int

  val coq_lxor : int -> int -> int

  val abs : int -> int
 end

type literal = int

type clause = literal list

type cNF = clause list

val var_cell_digit : int -> int -> int -> int -> int

val at_least_one_clause : int -> int -> int -> clause

val at_most_one_clauses_aux :
  int -> int -> int -> int -> int list -> clause list

val at_most_one_clauses : int -> int -> int -> int list -> clause list

val exactly_one_cell : int -> int -> int -> cNF

val row_unique_aux : int -> int -> int -> int -> int list -> clause list

val row_unique_digit : int -> int -> int -> int list -> clause list

val row_unique : int -> int -> int -> cNF

val col_unique_aux : int -> int -> int -> int -> int list -> clause list

val col_unique_digit : int -> int -> int -> int list -> clause list

val col_unique : int -> int -> int -> cNF

val latin_cnf : int -> cNF

type cell = int*int

type cageOp =
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpXor
| OpMod

type cage = { cage_cells : cell list; cage_op : cageOp; cage_target : int }

val all_tuples : int -> int -> int list list

val eval_op : cageOp -> int -> int list -> int option

val valid_tuples : int -> cage -> int list list

val tuple_aux_var : int -> int -> int -> int

val encode_tuple_forward : int -> cell list -> int list -> int -> cNF

val encode_tuple_backward : int -> cell list -> int list -> int -> clause

val encode_cage : int -> int -> int -> cage -> cNF

val clause_to_dimacs : clause -> int list

val cnf_to_dimacs : cNF -> int list list

val count_variables : cNF -> int

val count_clauses : cNF -> int
