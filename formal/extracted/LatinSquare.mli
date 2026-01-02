
val xorb : bool -> bool -> bool

val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val sub : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val max : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val div2 : int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_lxor : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type cell = int*int

type constraint0 =
| CellFilled of int * int
| RowValue of int * int
| ColValue of int * int

type placement = { pl_row : int; pl_col : int; pl_val : int }

val placement_constraints : int -> placement -> constraint0 list

val all_placements : int -> placement list

type cageOp =
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpXor
| OpMod

type cage = { cage_cells : cell list; cage_op : cageOp; cage_target : int }

val eval_cage : int -> cage -> int list -> int option
