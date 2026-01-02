
type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val of_succ_nat : int -> int
 end

module Coq_Pos :
 sig
  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int
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

  val compare : int -> int -> comparison

  val of_nat : int -> int

  val gtb : int -> int -> bool
 end

val fact_nat : int -> int

val fact_z : int -> int

val reduced_count_z : int -> int

val latin_count_z : int -> int

val stirling2_z : int -> int -> int -> int

val stirling2 : int -> int -> int

val sum_stirling_z : int -> int -> int -> int

val bell_z : int -> int

val mODE_STANDARD : int

val mODE_MULTIPLICATION : int

val mODE_MYSTERY : int

val mODE_ZERO_INCLUSIVE : int

val mODE_NEGATIVE : int

val mODE_EXPONENT : int

val mODE_MODULAR : int

val mODE_KILLER : int

val mODE_HINT : int

val mODE_ADAPTIVE : int

val mODE_STORY : int

val mODE_BITWISE : int

val solution_space_z : int -> int
