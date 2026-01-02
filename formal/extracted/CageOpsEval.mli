
val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2



val mul : int -> int -> int

val sub : int -> int -> int

val divmod : int -> int -> int -> int -> int*int

val div : int -> int -> int

val modulo : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val max : int -> int -> int

  val min : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val gcd : int -> int -> int

  val div2 : int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_land : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_lxor : int -> int -> int

  val lcm : int -> int -> int
 end

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

module Pos :
 sig
  val succ : int -> int

  val eqb : int -> int -> bool

  val of_succ_nat : int -> int
 end

module Z :
 sig
  val eqb : int -> int -> bool

  val of_nat : int -> int
 end

type cell = int*int

type cageOp =
| OpAdd
| OpXor
| OpMul
| OpAnd
| OpSub
| OpOr
| OpDiv
| OpExp
| OpMod
| OpGcd
| OpLcm

type clue = { clue_op : cageOp; clue_value : int }

type cage = { cage_cells : cell list; cage_clue : clue }

val gcd0 : int -> int -> int

val lcm0 : int -> int -> int

val pow : int -> int -> int

val fold_add : int list -> int

val fold_mul : int list -> int

val fold_xor : int list -> int

val fold_and : int list -> int

val fold_or : int list -> int

val fold_gcd : int list -> int

val fold_lcm : int list -> int

val eval_add : int list -> int option

val eval_mul : int list -> int option

val eval_sub : int list -> int option

val eval_div : int list -> int option

val eval_exp : int list -> int option

val eval_mod : int list -> int option

val eval_xor : int list -> int option

val eval_and : int list -> int option

val eval_or : int list -> int option

val eval_gcd : int list -> int option

val eval_lcm : int list -> int option

val eval_cage_op : cageOp -> int list -> int option

val cage_satisfiedb : cage -> int list -> bool

type opClass = { oc_op : cageOp; oc_binary_only : bool;
                 oc_commutative : bool; oc_associative : bool;
                 oc_identity : int option }

val classify_op : cageOp -> opClass
