
val negb : bool -> bool

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val even : int -> bool

  val odd : int -> bool

  val div2 : int -> int

  val testbit : int -> int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val repeat : 'a1 -> int -> 'a1 list

val nth : int -> 'a1 list -> 'a1 -> 'a1

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list

type digit = int

type cell = int*int

type gridList = digit list

type candidates = int

type possibilityCube = bool list

val cubepos : int -> int -> int -> int -> int

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

type solverResult =
| SolvedAt of difficulty
| Impossible
| Ambiguous
| Unfinished

val list_set : 'a1 list -> int -> 'a1 -> 'a1 list

val cube_possible : int -> possibilityCube -> int -> int -> int -> bool

val cube_set :
  int -> possibilityCube -> int -> int -> int -> bool -> possibilityCube

val cube_eliminate :
  int -> possibilityCube -> int -> int -> int -> possibilityCube

val count_true : bool list -> int

val cell_possibilities : int -> possibilityCube -> int -> int -> int

val cell_unique_digit : int -> possibilityCube -> int -> int -> int option

val propagate_row :
  int -> possibilityCube -> int -> int -> int -> possibilityCube

val propagate_col :
  int -> possibilityCube -> int -> int -> int -> possibilityCube

type placeResult = { pr_cube : possibilityCube; pr_grid : gridList }

val place_digit :
  int -> possibilityCube -> gridList -> int -> int -> int -> placeResult

type iscratchPerCell = candidates list

val init_iscratch_cells : int -> iscratchPerCell

type cageResult = { cr_cube : possibilityCube; cr_changed : bool }

val apply_iscratch_cells :
  int -> possibilityCube -> cell list -> iscratchPerCell -> cageResult

type solverConfig = { sc_diff : difficulty; sc_use_easy : bool;
                      sc_use_normal : bool; sc_use_hard : bool;
                      sc_use_forcing : bool; sc_use_recursion : bool }

val config_easy : solverConfig

val config_normal : solverConfig

val config_hard : solverConfig

val config_extreme : solverConfig

val config_unreasonable : solverConfig

type solverState = { ss_cube : possibilityCube; ss_grid : gridList;
                     ss_changed : bool }

val ss_cube : solverState -> possibilityCube

val ss_grid : solverState -> gridList

val ss_changed : solverState -> bool

val init_solver_state : int -> solverState

val grid_complete_check : int -> gridList -> bool

val elimination_pass :
  int -> solverConfig -> cage list -> solverState -> solverState

val solver_loop :
  int -> int -> solverConfig -> cage list -> solverState -> solverState

val check_solver_result : int -> solverState -> solverResult
