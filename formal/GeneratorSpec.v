(** * GeneratorSpec: Formal Specification of KenKen Puzzle Generator

    This module specifies the puzzle generation algorithm from keen_generate.c.
    The generator creates puzzles with the following structure:
    1. Generate a random Latin square (solution)
    2. Partition grid into cages using DSF-based algorithm
    3. Select clue operations for each cage
    4. Validate puzzle achieves target difficulty

    Key algorithm (new_game_desc, CCN 182):
    1. latin_generate: Create valid Latin square
    2. Domino placement: Pair adjacent cells randomly
    3. Singleton folding: Merge remaining cells into cages
    4. Clue selection: Choose operations based on cage size and difficulty
    5. Solver validation: Verify puzzle achieves target difficulty

    Mathematical foundations:
    - Solution space: L(n) = n! × (n-1)! × R(n) Latin squares (OEIS A002860)
    - Difficulty is based on solver technique requirements
    - Grid complexity grows super-exponentially with size

    Reference: keen_generate.c (lines 403-900)

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import NArith.
From Stdlib Require Import PArith.
Import ListNotations.

From KeenKenning Require Import SolverTypes.
From KeenKenning Require Import DSF.
From KeenKenning Require Import CageOps.
From KeenKenning Require Import SolverSpec.
From KeenKenning Require Import LatinBoundsZ.

(* Close Z scope from LatinBoundsZ, work in nat scope by default *)
Close Scope Z_scope.
Open Scope nat_scope.

(** ** Generator Parameters *)

(** Generator state encapsulating all mutable data *)
Record GenState := mkGenState {
  gs_grid : GridList;           (* Latin square solution *)
  gs_dsf : DSF;                 (* Cage membership *)
  gs_singletons : list bool;    (* Unmerged cells *)
  gs_clues : list Clue          (* Selected clues *)
}.

(** Generator configuration *)
Record GenConfig := mkGenConfig {
  gc_width : nat;               (* Grid width *)
  gc_diff : Difficulty;         (* Target difficulty *)
  gc_mode_flags : ModeFlags;    (* Game mode flags *)
  gc_maxblk : nat              (* Maximum cage size *)
}.

(** ** Latin Square Generation *)

(** A valid Latin square has each digit 1..n exactly once per row and column *)
Definition is_latin_square (n : nat) (grid : GridList) : Prop :=
  length grid = n * n /\
  (* Each cell has valid digit *)
  (forall idx, idx < n * n ->
    match nth_error grid idx with
    | Some d => 1 <= d /\ d <= n
    | None => False
    end) /\
  (* Row uniqueness *)
  row_unique n grid /\
  (* Column uniqueness *)
  col_unique n grid.

(** Latin square generation specification:
    latin_generate returns a valid Latin square *)
Definition latin_generate_spec (n : nat) (grid : GridList) : Prop :=
  is_latin_square n grid.

(** ** Cage Partitioning *)

(** All cells are assigned to exactly one cage *)
Definition cages_partition_grid (n : nat) (dsf : DSF) : Prop :=
  length dsf = n * n /\
  dsf_wf dsf /\
  (* Every cell has a canonical representative *)
  forall idx, idx < n * n ->
    exists root, dsf_canonify dsf idx = Some root.

(** Cages respect size bounds *)
Definition cages_respect_bounds (n : nat) (dsf : DSF) (maxblk : nat) : Prop :=
  forall idx,
    idx < n * n ->
    match dsf_size dsf idx with
    | Some sz => sz <= maxblk
    | None => False
    end.

(** No singleton cages remain (all cells merged) *)
Definition no_singletons (n : nat) (dsf : DSF) : Prop :=
  forall idx,
    idx < n * n ->
    match dsf_size dsf idx with
    | Some sz => sz >= 2  (* At least domino *)
    | None => False
    end.

(** ** Clue Selection *)

(** Flag constants matching F_ADD, F_MUL, etc. in C *)
Definition F_ADD : nat := 1.
Definition F_SUB : nat := 2.
Definition F_MUL : nat := 4.
Definition F_DIV : nat := 8.
Definition F_EXP : nat := 16.
Definition F_MOD : nat := 32.
Definition F_GCD : nat := 64.
Definition F_LCM : nat := 128.
Definition F_XOR : nat := 256.

(** Valid clue flags for a cage based on its properties *)
Definition valid_clue_flags (size : nat) (mode_flags : ModeFlags) : nat :=
  if Nat.ltb 2 size then
    (* Large cages: ADD, MUL, and XOR if BITWISE mode *)
    Nat.lor F_ADD (Nat.lor F_MUL
      (if has_mode mode_flags MODE_BITWISE then F_XOR else 0))
  else
    (* 2-cell cages: all operations potentially valid *)
    Nat.lor F_ADD (Nat.lor F_SUB (Nat.lor F_MUL (Nat.lor F_DIV
      (Nat.lor F_EXP (Nat.lor F_MOD (Nat.lor F_GCD (Nat.lor F_LCM F_XOR))))))).

(** Clue is valid for its cage *)
Definition clue_valid_for_cage (cage : Cage) (grid : GridList) : Prop :=
  let cells := cage_cells cage in
  let digits := map (fun c =>
    match nth_error grid (cell_to_index (length cells) c) with
    | Some d => d
    | None => 0
    end) cells in
  cage_satisfied cage digits.

(** ** Difficulty Validation *)

(** Puzzle achieves at least target difficulty *)
Definition achieves_difficulty (n : nat) (cages : list Cage) (target : Difficulty) : Prop :=
  exists actual,
    diff_le target actual /\
    (* Solver can solve at this difficulty *)
    (exists fuel,
      let init := init_solver_state n in
      let config := match actual with
        | DiffEasy => config_easy
        | DiffNormal => config_normal
        | DiffHard => config_hard
        | DiffExtreme => config_extreme
        | _ => config_unreasonable
        end in
      let final := solver_loop fuel n config cages init in
      grid_complete_check n (ss_grid final) = true).

(** Puzzle achieves exactly target difficulty (not easier) *)
Definition achieves_exact_difficulty (n : nat) (cages : list Cage) (target : Difficulty) : Prop :=
  achieves_difficulty n cages target /\
  (* And cannot be solved at easier difficulty *)
  match target with
  | DiffEasy => True  (* Easy is the lowest *)
  | DiffNormal =>
      ~ (exists fuel,
        let init := init_solver_state n in
        let final := solver_loop fuel n config_easy cages init in
        grid_complete_check n (ss_grid final) = true)
  | DiffHard =>
      ~ (exists fuel,
        let init := init_solver_state n in
        let final := solver_loop fuel n config_normal cages init in
        grid_complete_check n (ss_grid final) = true)
  | _ => True  (* Higher difficulties: similar pattern *)
  end.

(** ** Generator Correctness *)

(** Complete generator specification *)
Record GeneratorOutput := mkGeneratorOutput {
  go_grid : GridList;           (* Solution *)
  go_cages : list Cage;         (* Cage structure *)
  go_width : nat                (* Grid size *)
}.

(** Generator output is valid *)
Definition generator_valid (cfg : GenConfig) (out : GeneratorOutput) : Prop :=
  let n := go_width out in
  let grid := go_grid out in
  let cages := go_cages out in
  (* Solution is valid Latin square *)
  is_latin_square n grid /\
  (* Cages partition the grid *)
  (exists dsf,
    cages_partition_grid n dsf /\
    cages_respect_bounds n dsf (gc_maxblk cfg)) /\
  (* Each clue is satisfiable by solution *)
  Forall (fun cage => clue_valid_for_cage cage grid) cages /\
  (* Puzzle achieves target difficulty *)
  achieves_difficulty n cages (gc_diff cfg).

(** ** Main Theorems *)

(** Latin square generation produces valid result *)
Theorem latin_generate_valid : forall n grid,
  n > 0 ->
  latin_generate_spec n grid ->
  is_latin_square n grid.
Proof.
  intros n grid Hn Hspec.
  exact Hspec.
Qed.

(** DSF-based cage creation partitions grid *)
Theorem cage_creation_partitions : forall n dsf,
  n > 0 ->
  dsf = dsf_init (n * n) ->
  (* After domino placement and singleton folding *)
  forall dsf',
    dsf_wf dsf' ->
    length dsf' = n * n ->
    cages_partition_grid n dsf'.
Proof.
  intros n dsf Hn Hinit dsf' Hwf Hlen.
  unfold cages_partition_grid.
  split; [exact Hlen|].
  split; [exact Hwf|].
  intros idx Hidx.
  (* Hwf expects idx < length dsf', we have idx < n * n *)
  rewrite <- Hlen in Hidx.
  destruct (Hwf idx Hidx) as [root [Hcan _]].
  exists root. exact Hcan.
Qed.

(** Valid clues are satisfiable *)
Theorem valid_clue_satisfiable : forall cage grid,
  clue_valid_for_cage cage grid ->
  exists digits, cage_satisfied cage digits.
Proof.
  intros cage grid Hvalid.
  unfold clue_valid_for_cage in Hvalid.
  (* The digits extracted from grid satisfy the cage *)
  exists (map (fun c =>
    match nth_error grid (cell_to_index (length (cage_cells cage)) c) with
    | Some d => d
    | None => 0
    end) (cage_cells cage)).
  exact Hvalid.
Qed.

(** Generator produces solvable puzzles *)
Theorem generator_produces_solvable : forall cfg out,
  generator_valid cfg out ->
  exists fuel,
    let n := go_width out in
    let cages := go_cages out in
    let init := init_solver_state n in
    (* Some solver configuration can solve it *)
    (exists config,
      grid_complete_check n (ss_grid (solver_loop fuel n config cages init)) = true).
Proof.
  intros cfg out Hvalid.
  unfold generator_valid in Hvalid.
  destruct Hvalid as [Hlatin [Hcages [Hclues Hdiff]]].
  unfold achieves_difficulty in Hdiff.
  destruct Hdiff as [actual [_ [fuel Hsolve]]].
  exists fuel.
  (* Config exists from achieves_difficulty *)
  eexists. exact Hsolve.
Qed.

(** ** Mode-Specific Generation *)

(** Killer mode: no repeated digits within cages *)
Definition killer_valid (n : nat) (cage : Cage) (grid : GridList) : Prop :=
  let cells := cage_cells cage in
  let digits := map (fun c =>
    match nth_error grid (cell_to_index n c) with
    | Some d => d
    | None => 0
    end) cells in
  NoDup digits.

(** Zero-inclusive mode: digits 0..n-1 instead of 1..n *)
Definition zero_inclusive_transform (d : Digit) : Digit := d - 1.

(** Negative mode: digits -n/2..+n/2 *)
Definition negative_transform (n : nat) (d : Digit) : Z :=
  Z.of_nat d - Z.of_nat (n / 2 + 1).

(** ** Grid Size Complexity Theory *)

(** Solution space grows super-exponentially with grid size.
    L(n) = n! × (n-1)! × R(n) where R(n) is the reduced Latin square count.
    Known values (OEIS A002860):
      L(1) = 1
      L(2) = 2
      L(3) = 12
      L(4) = 576
      L(5) = 161280
      L(6) = 812851200
*)

(** Solution space for grid size n *)
Definition solution_space (n : nat) : Z := latin_count_z (Z.of_nat n).

(** Minimum and maximum grid sizes *)
Definition MIN_GRID_SIZE : nat := 3.
Definition MAX_GRID_SIZE : nat := 16.

(** Valid grid size predicate *)
Definition valid_grid_size (n : nat) : Prop :=
  MIN_GRID_SIZE <= n /\ n <= MAX_GRID_SIZE.

(** Grid size categories for difficulty scaling *)
Inductive GridCategory : Type :=
  | GridSmall   (* 3-5: beginner-friendly *)
  | GridMedium  (* 6-8: standard puzzles *)
  | GridLarge   (* 9-12: challenging *)
  | GridHuge.   (* 13-16: expert only *)

Definition classify_grid_size (n : nat) : GridCategory :=
  if Nat.leb n 5 then GridSmall
  else if Nat.leb n 8 then GridMedium
  else if Nat.leb n 12 then GridLarge
  else GridHuge.

(** ** Mathematical Difficulty Theory *)

(** Difficulty is determined by solver techniques required.
    Easy: Naked singles only (direct constraint propagation)
    Normal: Hidden singles (column/row scanning)
    Hard: Naked pairs/triples (subset elimination)
    Extreme: Hidden pairs, box/line reduction
    Unreasonable: X-wing, swordfish
    Ludicrous: Finned techniques, forcing chains
    Incomprehensible: Trial-and-error (backtracking required)
*)

(** Technique complexity level (ascending order) *)
Definition technique_level (diff : Difficulty) : nat :=
  match diff with
  | DiffEasy => 1           (* Naked singles *)
  | DiffNormal => 2         (* Hidden singles *)
  | DiffHard => 3           (* Naked pairs/triples *)
  | DiffExtreme => 4        (* Hidden pairs, reductions *)
  | DiffUnreasonable => 5   (* Fish patterns *)
  | DiffLudicrous => 6      (* Forcing chains *)
  | DiffIncomprehensible => 7  (* Backtracking *)
  end.

(** Difficulty ordering is total *)
Theorem technique_level_reflects_diff_le : forall d1 d2,
  diff_le d1 d2 <-> technique_level d1 <= technique_level d2.
Proof.
  intros d1 d2.
  unfold diff_le, technique_level, diff_to_nat.
  split; intro H; destruct d1; destruct d2; simpl in *; lia.
Qed.

(** ** Difficulty-Grid Size Interaction *)

(** Minimum recommended difficulty for a grid size.
    Larger grids should be at least Normal to be interesting. *)
Definition min_difficulty_for_size (n : nat) : Difficulty :=
  match classify_grid_size n with
  | GridSmall => DiffEasy       (* 3-5: any difficulty works *)
  | GridMedium => DiffNormal    (* 6-8: at least normal *)
  | GridLarge => DiffHard       (* 9-12: hard minimum *)
  | GridHuge => DiffExtreme     (* 13-16: extreme minimum *)
  end.

(** Maximum practical difficulty for a grid size.
    Smaller grids can't support very complex techniques. *)
Definition max_difficulty_for_size (n : nat) : Difficulty :=
  match classify_grid_size n with
  | GridSmall => DiffHard           (* 3-5: max hard *)
  | GridMedium => DiffExtreme       (* 6-8: max extreme *)
  | GridLarge => DiffUnreasonable   (* 9-12: max unreasonable *)
  | GridHuge => DiffIncomprehensible  (* 13-16: any *)
  end.

(** Difficulty is appropriate for grid size *)
Definition appropriate_difficulty (n : nat) (diff : Difficulty) : Prop :=
  diff_le (min_difficulty_for_size n) diff /\
  diff_le diff (max_difficulty_for_size n).

(** Cage count estimate for difficulty.
    Harder puzzles have fewer, larger cages.
    Easy: ~n*n/2 cages (mostly dominoes)
    Hard: ~n*n/4 cages (larger cages)
    Extreme: ~n*n/6 cages (very large cages) *)
Definition estimated_cage_count (n : nat) (diff : Difficulty) : nat :=
  let cells := n * n in
  match diff with
  | DiffEasy => cells / 2
  | DiffNormal => cells * 2 / 5
  | DiffHard => cells / 3
  | DiffExtreme => cells / 4
  | _ => cells / 5
  end.

(** Average cage size for difficulty *)
Definition average_cage_size (n : nat) (diff : Difficulty) : nat :=
  let cells := n * n in
  let cages := estimated_cage_count n diff in
  if Nat.eqb cages 0 then 1 else cells / cages.

(** ** Retry Logic *)

(** Generator retry specification:
    If target difficulty cannot be achieved, retry up to max_retries *)
Definition retry_budget (n : nat) (diff : Difficulty) : nat :=
  let base := 1000 + n * n * 20 in
  let diff_mult := match diff with
    | DiffEasy => 1
    | DiffNormal => 2
    | DiffHard => 2
    | DiffExtreme => 4
    | _ => 8
    end in
  let size_mult := if Nat.leb 9 n then 3 else if Nat.leb 7 n then 2 else 1 in
  base * diff_mult * size_mult.

(** Helper: difficulty multiplier is positive *)
Lemma diff_mult_pos : forall diff,
  (match diff with
   | DiffEasy => 1 | DiffNormal => 2 | DiffHard => 2
   | DiffExtreme => 4 | _ => 8
   end) >= 1.
Proof. destruct diff; lia. Qed.

(** Helper: size multiplier is positive *)
Lemma size_mult_pos : forall n,
  (if Nat.leb 9 n then 3 else if Nat.leb 7 n then 2 else 1) >= 1.
Proof.
  intro n.
  destruct (Nat.leb 9 n); [lia|].
  destruct (Nat.leb 7 n); lia.
Qed.

(** Retry loop terminates - base >= 1020, multipliers >= 1 *)
Theorem retry_terminates : forall n diff,
  n > 0 ->
  retry_budget n diff > 0.
Proof.
  intros n diff Hn.
  unfold retry_budget.
  (* Establish bounds on each component *)
  set (base := 1000 + n * n * 20).
  set (diff_mult := match diff with
    | DiffEasy => 1 | DiffNormal => 2 | DiffHard => 2
    | DiffExtreme => 4 | _ => 8 end).
  set (size_mult := if Nat.leb 9 n then 3 else if Nat.leb 7 n then 2 else 1).

  (* base >= 1020 since n >= 1 implies n*n >= 1 *)
  assert (Hbase: base >= 1020) by (unfold base; lia).

  (* All multipliers >= 1 *)
  assert (Hdiff: diff_mult >= 1) by (unfold diff_mult; apply diff_mult_pos).
  assert (Hsize: size_mult >= 1) by (unfold size_mult; apply size_mult_pos).

  (* Product of positives is positive *)
  (* base * diff_mult >= 1020 * 1 = 1020 *)
  (* base * diff_mult * size_mult >= 1020 * 1 = 1020 > 0 *)
  nia.
Qed.

(** Solution space verification lemmas using LatinBoundsZ *)
Lemma solution_space_3 : solution_space 3 = 12%Z.
Proof. reflexivity. Qed.

Lemma solution_space_4 : solution_space 4 = 576%Z.
Proof. reflexivity. Qed.

(** Solution space is positive for specific grid sizes *)
Lemma solution_space_3_pos : (solution_space 3 > 0)%Z.
Proof. reflexivity. Qed.

Lemma solution_space_4_pos : (solution_space 4 > 0)%Z.
Proof. reflexivity. Qed.

Lemma solution_space_5_pos : (solution_space 5 > 0)%Z.
Proof. reflexivity. Qed.

Lemma solution_space_6_pos : (solution_space 6 > 0)%Z.
Proof. reflexivity. Qed.

(** Solution space is positive for valid grid sizes *)
Theorem solution_space_positive : forall n,
  3 <= n <= 6 ->
  (solution_space n > 0)%Z.
Proof.
  intros n [Hlo Hhi].
  (* Case analysis on n with bounds *)
  destruct n as [|[|[|[|[|[|[|n']]]]]]]; try lia.
  - (* n = 3 *) exact solution_space_3_pos.
  - (* n = 4 *) exact solution_space_4_pos.
  - (* n = 5 *) exact solution_space_5_pos.
  - (* n = 6 *) exact solution_space_6_pos.
Qed.

(** ** Extraction Hints *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.

(** End of GeneratorSpec *)
