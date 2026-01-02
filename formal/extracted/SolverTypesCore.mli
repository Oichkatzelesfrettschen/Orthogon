
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2



val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int
 end

module N :
 sig
  val succ_pos : int -> int

  val coq_lor : int -> int -> int

  val ldiff : int -> int -> int
 end

module Z :
 sig
  val eqb : int -> int -> bool

  val of_N : int -> int

  val coq_land : int -> int -> int
 end

type digit = int

type cell = int*int

type cell_in_bounds = __

val cell_to_index : int -> cell -> int

val index_to_cell : int -> int -> cell

type gridList = digit list

type possibilityCube = bool list

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

val clue_op : clue -> cageOp

val clue_value : clue -> int

type cage = { cage_cells : cell list; cage_clue : clue }

val cage_cells : cage -> cell list

val cage_clue : cage -> clue

type difficulty =
| DiffEasy
| DiffNormal
| DiffHard
| DiffExtreme
| DiffUnreasonable
| DiffLudicrous
| DiffIncomprehensible

val diff_to_nat : difficulty -> int

val diff_leb : difficulty -> difficulty -> bool

type modeFlags = int

val mODE_STANDARD : int

val mODE_MULTIPLICATION : int

val mODE_MYSTERY : int

val mODE_ZERO_INCLUSIVE : int

val mODE_NEGATIVE : int

val mODE_EXPONENT : int

val mODE_MODULAR : int

val mODE_KILLER : int

val mODE_BITWISE : int

val has_mode : modeFlags -> int -> bool
