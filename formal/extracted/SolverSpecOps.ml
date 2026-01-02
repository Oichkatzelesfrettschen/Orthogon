
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val testbit : int -> int -> bool **)

  let rec testbit = (fun n k -> (n lsr k) land 1 = 1)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::l0 -> (f a)::(map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start::(seq (succ start) len0))
    len

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x::(repeat x k))
    n

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x::_ -> x)
    (fun m -> match l with
              | [] -> default
              | _::l' -> nth m l' default)
    n

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a::l0 -> a::(firstn n0 l0))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n0 -> match l with
               | [] -> []
               | _::l0 -> skipn n0 l0)
    n

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::l0 -> fold_left f l0 (f a0 b)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl -> (match l' with
              | [] -> []
              | y::tl' -> (x,y)::(combine tl tl'))

type digit = int

type cell = int*int

type gridList = digit list

type candidates = int

type possibilityCube = bool list

(** val cubepos : int -> int -> int -> int -> int **)

let cubepos o x y d =
  sub (add (mul (add (mul x o) y) o) d) (succ 0)

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

(** val list_set : 'a1 list -> int -> 'a1 -> 'a1 list **)

let rec list_set l idx v =
  match l with
  | [] -> []
  | h::t ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> v::t)
       (fun n -> h::(list_set t n v))
       idx)

(** val cube_possible :
    int -> possibilityCube -> int -> int -> int -> bool **)

let cube_possible o cube x y n =
  nth (cubepos o x y n) cube false

(** val cube_set :
    int -> possibilityCube -> int -> int -> int -> bool -> possibilityCube **)

let cube_set o cube x y n v =
  let pos = cubepos o x y n in
  app (firstn pos cube) (app (v::[]) (skipn (succ pos) cube))

(** val cube_eliminate :
    int -> possibilityCube -> int -> int -> int -> possibilityCube **)

let cube_eliminate o cube x y n =
  cube_set o cube x y n false

(** val count_true : bool list -> int **)

let rec count_true = function
| [] -> 0
| b::rest -> if b then succ (count_true rest) else count_true rest

(** val cell_possibilities : int -> possibilityCube -> int -> int -> int **)

let cell_possibilities o cube x y =
  count_true (map (fun n -> cube_possible o cube x y n) (seq (succ 0) o))

(** val cell_unique_digit :
    int -> possibilityCube -> int -> int -> int option **)

let cell_unique_digit o cube x y =
  let poss = filter (fun n -> cube_possible o cube x y n) (seq (succ 0) o) in
  (match poss with
   | [] -> None
   | n::l -> (match l with
              | [] -> Some n
              | _::_ -> None))

(** val propagate_row :
    int -> possibilityCube -> int -> int -> int -> possibilityCube **)

let propagate_row o cube y n except_x =
  fold_left (fun c x ->
    if (=) x except_x then c else cube_eliminate o c x y n) (seq 0 o) cube

(** val propagate_col :
    int -> possibilityCube -> int -> int -> int -> possibilityCube **)

let propagate_col o cube x n except_y =
  fold_left (fun c y ->
    if (=) y except_y then c else cube_eliminate o c x y n) (seq 0 o) cube

type placeResult = { pr_cube : possibilityCube; pr_grid : gridList }

(** val place_digit :
    int -> possibilityCube -> gridList -> int -> int -> int -> placeResult **)

let place_digit o cube grid x y n =
  let grid' = list_set grid (add (mul y o) x) n in
  let cube' =
    fold_left (fun c d -> if (=) d n then c else cube_eliminate o c x y d)
      (seq (succ 0) o) cube
  in
  let cube'' = propagate_row o cube' y n x in
  let cube''' = propagate_col o cube'' x n y in
  { pr_cube = cube'''; pr_grid = grid' }

type iscratchPerCell = candidates list

(** val init_iscratch_cells : int -> iscratchPerCell **)

let init_iscratch_cells n =
  repeat 0 n

type cageResult = { cr_cube : possibilityCube; cr_changed : bool }

(** val apply_iscratch_cells :
    int -> possibilityCube -> cell list -> iscratchPerCell -> cageResult **)

let apply_iscratch_cells o cube cells iscratch =
  let indexed = combine cells iscratch in
  fold_left (fun res pair ->
    let y0,mask = pair in
    let x,y = y0 in
    fold_left (fun res' d ->
      if (&&) (cube_possible o res'.cr_cube x y d) (negb (Nat.testbit mask d))
      then { cr_cube = (cube_eliminate o res'.cr_cube x y d); cr_changed =
             true }
      else res') (seq (succ 0) o) res)
    indexed { cr_cube = cube; cr_changed = false }

type solverConfig = { sc_diff : difficulty; sc_use_easy : bool;
                      sc_use_normal : bool; sc_use_hard : bool;
                      sc_use_forcing : bool; sc_use_recursion : bool }

(** val config_easy : solverConfig **)

let config_easy =
  { sc_diff = DiffEasy; sc_use_easy = true; sc_use_normal = false;
    sc_use_hard = false; sc_use_forcing = false; sc_use_recursion = false }

(** val config_normal : solverConfig **)

let config_normal =
  { sc_diff = DiffNormal; sc_use_easy = false; sc_use_normal = true;
    sc_use_hard = false; sc_use_forcing = false; sc_use_recursion = false }

(** val config_hard : solverConfig **)

let config_hard =
  { sc_diff = DiffHard; sc_use_easy = false; sc_use_normal = true;
    sc_use_hard = true; sc_use_forcing = false; sc_use_recursion = false }

(** val config_extreme : solverConfig **)

let config_extreme =
  { sc_diff = DiffExtreme; sc_use_easy = false; sc_use_normal = true;
    sc_use_hard = true; sc_use_forcing = true; sc_use_recursion = false }

(** val config_unreasonable : solverConfig **)

let config_unreasonable =
  { sc_diff = DiffUnreasonable; sc_use_easy = false; sc_use_normal = true;
    sc_use_hard = true; sc_use_forcing = true; sc_use_recursion = true }

type solverState = { ss_cube : possibilityCube; ss_grid : gridList;
                     ss_changed : bool }

(** val ss_cube : solverState -> possibilityCube **)

let ss_cube s =
  s.ss_cube

(** val ss_grid : solverState -> gridList **)

let ss_grid s =
  s.ss_grid

(** val ss_changed : solverState -> bool **)

let ss_changed s =
  s.ss_changed

(** val init_solver_state : int -> solverState **)

let init_solver_state o =
  { ss_cube = (repeat true (mul (mul o o) o)); ss_grid =
    (repeat 0 (mul o o)); ss_changed = false }

(** val grid_complete_check : int -> gridList -> bool **)

let grid_complete_check _ grid =
  forallb (fun d -> negb ((=) d 0)) grid

(** val elimination_pass :
    int -> solverConfig -> cage list -> solverState -> solverState **)

let elimination_pass o config cages state =
  fold_left (fun st cage0 ->
    let cells = cage0.cage_cells in
    let n = length cells in
    let iscratch = init_iscratch_cells n in
    if config.sc_use_normal
    then let res = apply_iscratch_cells o st.ss_cube cells iscratch in
         { ss_cube = res.cr_cube; ss_grid = st.ss_grid; ss_changed =
         ((||) st.ss_changed res.cr_changed) }
    else st) cages state

(** val solver_loop :
    int -> int -> solverConfig -> cage list -> solverState -> solverState **)

let rec solver_loop fuel o config cages state =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> state)
    (fun fuel' ->
    let state' =
      elimination_pass o config cages { ss_cube = state.ss_cube; ss_grid =
        state.ss_grid; ss_changed = false }
    in
    if state'.ss_changed
    then solver_loop fuel' o config cages state'
    else state')
    fuel

(** val check_solver_result : int -> solverState -> solverResult **)

let check_solver_result o state =
  if grid_complete_check o state.ss_grid
  then SolvedAt DiffNormal
  else Unfinished
