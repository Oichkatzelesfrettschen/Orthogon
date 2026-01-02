
val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val div : int -> int -> int

  val div2 : int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_lor : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val of_succ_nat : int -> int
 end

module Coq_Pos :
 sig
  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int
 end

module N :
 sig
  val succ_pos : int -> int

  val coq_lor : int -> int -> int

  val ldiff : int -> int -> int
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

  val eqb : int -> int -> bool

  val of_nat : int -> int

  val of_N : int -> int

  val coq_land : int -> int -> int

  val gtb : int -> int -> bool
 end

type digit = int

type cell = int*int

type gridList = digit list

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

type difficulty =
| DiffEasy
| DiffNormal
| DiffHard
| DiffExtreme
| DiffUnreasonable
| DiffLudicrous
| DiffIncomprehensible

type modeFlags = int

val has_mode : modeFlags -> int -> bool

type dSF = int list

val fact_nat : int -> int

val fact_z : int -> int

val reduced_count_z : int -> int

val latin_count_z : int -> int

val mODE_BITWISE : int

type genState = { gs_grid : gridList; gs_dsf : dSF;
                  gs_singletons : bool list; gs_clues : clue list }

val gs_grid : genState -> gridList

val gs_dsf : genState -> dSF

val gs_singletons : genState -> bool list

val gs_clues : genState -> clue list

type genConfig = { gc_width : int; gc_diff : difficulty;
                   gc_mode_flags : modeFlags; gc_maxblk : int }

val gc_width : genConfig -> int

val gc_diff : genConfig -> difficulty

val gc_mode_flags : genConfig -> modeFlags

val gc_maxblk : genConfig -> int

val f_ADD : int

val f_SUB : int

val f_MUL : int

val f_DIV : int

val f_EXP : int

val f_MOD : int

val f_GCD : int

val f_LCM : int

val f_XOR : int

val valid_clue_flags : int -> modeFlags -> int

type generatorOutput = { go_grid : gridList; go_cages : cage list;
                         go_width : int }

val go_grid : generatorOutput -> gridList

val go_cages : generatorOutput -> cage list

val go_width : generatorOutput -> int

val zero_inclusive_transform : digit -> digit

val negative_transform : int -> digit -> int

val solution_space : int -> int

val mIN_GRID_SIZE : int

val mAX_GRID_SIZE : int

type gridCategory =
| GridSmall
| GridMedium
| GridLarge
| GridHuge

val classify_grid_size : int -> gridCategory

val technique_level : difficulty -> int

val min_difficulty_for_size : int -> difficulty

val max_difficulty_for_size : int -> difficulty

val estimated_cage_count : int -> difficulty -> int

val average_cage_size : int -> difficulty -> int

val retry_budget : int -> difficulty -> int
