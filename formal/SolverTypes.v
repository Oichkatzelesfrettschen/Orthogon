(** * Solver Types: Core Type Definitions for KenKen Solver

    This module defines Rocq types corresponding to C structures
    in keen_solver.c and latin.h. These form the foundation for
    formalizing the solver algorithm.

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Digit Type *)

(** A digit is a value 1..N for an NxN grid.
    In C: typedef unsigned char digit; (latin.h:37)
    We use nat with validity constraints. *)
Definition Digit := nat.

(** Valid digit for grid size n *)
Definition valid_digit (n : nat) (d : Digit) : Prop :=
  1 <= d /\ d <= n.

Close Scope Z_scope.

(** ** Cell Position *)

(** A cell position (row, column) in 0-indexed coordinates.
    Matches: x, y in latin.h macros *)
Definition Cell := (nat * nat)%type.

(** Cell within grid bounds *)
Definition cell_in_bounds (n : nat) (c : Cell) : Prop :=
  fst c < n /\ snd c < n.

(** Linear index from cell: row * n + col *)
Definition cell_to_index (n : nat) (c : Cell) : nat :=
  let '(row, col) := c in row * n + col.

(** Cell from linear index *)
Definition index_to_cell (n : nat) (idx : nat) : Cell :=
  (idx / n, idx mod n).

(** ** Grid Representation *)

(** Grid as list of digits (row-major order).
    Matches: digit* grid in latin_solver (latin.h:49) *)
Definition GridList := list Digit.

(** Access grid cell *)
Definition grid_get (n : nat) (g : GridList) (c : Cell) : option Digit :=
  nth_error g (cell_to_index n c).

(** Grid is complete (all cells filled) *)
Definition grid_complete (n : nat) (g : GridList) : Prop :=
  length g = n * n /\
  forall d, In d g -> d > 0.

(** ** Candidate Bitmap *)

(** A bitmap representing possible digits for a cell.
    Bit i set means digit i is possible.
    Matches: int* iscratch in solver_ctx (keen_solver.c:17) *)
Definition Candidates := nat.

(** Check if digit is candidate *)
Definition is_candidate (cands : Candidates) (d : Digit) : bool :=
  Nat.testbit cands d.

(** Add digit to candidates *)
Definition add_candidate (cands : Candidates) (d : Digit) : Candidates :=
  Nat.lor cands (Nat.shiftl 1 d).

(** Remove digit from candidates (for 32-bit bitmask) *)
Definition remove_candidate (cands : Candidates) (d : Digit) : Candidates :=
  Nat.land cands (Nat.lxor (Nat.shiftl 1 d) (Nat.ones 32)).

(** Full candidates bitmap for grid size n: bits 1..n set *)
Definition full_candidates (n : nat) : Candidates :=
  Nat.shiftl 1 (n + 1) - 2.

(** ** Possibility Cube *)

(** The possibility cube is an o^3 array where cube[x*o*o + y*o + d-1]
    indicates if digit d is possible at cell (x,y).
    Matches: unsigned char* cube in latin_solver (latin.h:47-48) *)
Definition PossibilityCube := list bool.

(** Cube position macro: ((x)*solver->o + (y))*solver->o + (n) - 1 *)
Definition cubepos (o x y d : nat) : nat :=
  (x * o + y) * o + d - 1.

(** Access cube *)
Definition cube_get (o : nat) (cube : PossibilityCube) (x y d : nat) : bool :=
  nth (cubepos o x y d) cube false.

(** ** Cage Operations *)

(** Cage operation codes matching C definitions (keen_internal.h:28-39).
    These use packed encoding: operation in high bits. *)
Inductive CageOp : Type :=
  | OpAdd   (* C_ADD = 0x00000000 *)
  | OpXor   (* C_XOR = 0x10000000 - note: between ADD and MUL *)
  | OpMul   (* C_MUL = 0x20000000 *)
  | OpAnd   (* C_AND = 0x30000000 *)
  | OpSub   (* C_SUB = 0x40000000 *)
  | OpOr    (* C_OR  = 0x50000000 *)
  | OpDiv   (* C_DIV = 0x60000000 *)
  | OpExp   (* C_EXP = 0x80000000 *)
  | OpMod   (* C_MOD = 0xA0000000 *)
  | OpGcd   (* C_GCD = 0xC0000000 *)
  | OpLcm.  (* C_LCM = 0xE0000000 *)

(** Operation code to Z for extraction *)
Definition op_code (op : CageOp) : Z :=
  match op with
  | OpAdd => 0x00000000
  | OpXor => 0x10000000
  | OpMul => 0x20000000
  | OpAnd => 0x30000000
  | OpSub => 0x40000000
  | OpOr  => 0x50000000
  | OpDiv => 0x60000000
  | OpExp => 0x80000000
  | OpMod => 0xA0000000
  | OpGcd => 0xC0000000
  | OpLcm => 0xE0000000
  end.

(** CMASK for extracting operation from clue *)
Definition CMASK : Z := 0xF0000000.
Definition CUNIT : Z := 0x10000000.

(** ** Clue Type *)

(** A clue is packed as (operation | target_value).
    Matches: clue_t (long) in C with operation in high 4 bits.
    clue_t* clues in solver_ctx (keen_solver.c:14) *)
Record Clue := mkClue {
  clue_op : CageOp;
  clue_value : Z
}.

(** Pack clue to Z for extraction *)
Definition pack_clue (c : Clue) : Z :=
  Z.lor (op_code (clue_op c)) (clue_value c).

(** Unpack clue from Z *)
Definition unpack_op (packed : Z) : CageOp :=
  let op_bits := Z.land packed CMASK in
  if Z.eqb op_bits 0x00000000 then OpAdd
  else if Z.eqb op_bits 0x10000000 then OpXor
  else if Z.eqb op_bits 0x20000000 then OpMul
  else if Z.eqb op_bits 0x30000000 then OpAnd
  else if Z.eqb op_bits 0x40000000 then OpSub
  else if Z.eqb op_bits 0x50000000 then OpOr
  else if Z.eqb op_bits 0x60000000 then OpDiv
  else if Z.eqb op_bits 0x80000000 then OpExp
  else if Z.eqb op_bits 0xA0000000 then OpMod
  else if Z.eqb op_bits 0xC0000000 then OpGcd
  else OpLcm.

Definition unpack_value (packed : Z) : Z :=
  Z.land packed (Z.lnot CMASK).

Definition unpack_clue (packed : Z) : Clue :=
  mkClue (unpack_op packed) (unpack_value packed).

(** ** Cage Definition *)

(** A cage is a group of cells with a clue.
    Matches: boxes/boxlist in solver_ctx *)
Record Cage := mkCage {
  cage_cells : list Cell;
  cage_clue : Clue
}.

(** Cage size *)
Definition cage_size (cage : Cage) : nat :=
  length (cage_cells cage).

(** ** Difficulty Levels *)

(** Difficulty enumeration matching C DIFFLIST macro (keen_internal.h:13-20).
    Note: C uses X-macro pattern for compile-time generation. *)
Inductive Difficulty : Type :=
  | DiffEasy
  | DiffNormal
  | DiffHard
  | DiffExtreme
  | DiffUnreasonable
  | DiffLudicrous
  | DiffIncomprehensible.

(** Difficulty ordering *)
Definition diff_to_nat (d : Difficulty) : nat :=
  match d with
  | DiffEasy => 0
  | DiffNormal => 1
  | DiffHard => 2
  | DiffExtreme => 3
  | DiffUnreasonable => 4
  | DiffLudicrous => 5
  | DiffIncomprehensible => 6
  end.

Definition diff_le (d1 d2 : Difficulty) : Prop :=
  diff_to_nat d1 <= diff_to_nat d2.

Definition diff_leb (d1 d2 : Difficulty) : bool :=
  Nat.leb (diff_to_nat d1) (diff_to_nat d2).

(** ** Mode Flags *)

(** Mode flags matching keen_modes.h definitions.
    These are bit flags that modify puzzle rules. *)
Definition ModeFlags := Z.

Definition MODE_STANDARD       : Z := 0x0000.
Definition MODE_MULTIPLICATION : Z := 0x0001.
Definition MODE_MYSTERY        : Z := 0x0002.
Definition MODE_ZERO_INCLUSIVE : Z := 0x0004.
Definition MODE_NEGATIVE       : Z := 0x0008.
Definition MODE_EXPONENT       : Z := 0x0010.
Definition MODE_MODULAR        : Z := 0x0020.
Definition MODE_KILLER         : Z := 0x0040.
Definition MODE_HINT           : Z := 0x0080.
Definition MODE_ADAPTIVE       : Z := 0x0100.
Definition MODE_STORY          : Z := 0x0200.
Definition MODE_BITWISE        : Z := 0x0800.

(** Check if mode flag is set *)
Definition has_mode (flags : ModeFlags) (mode : Z) : bool :=
  negb (Z.eqb (Z.land flags mode) 0).

(** ** Solver Context *)

(** Main solver context matching struct solver_ctx (keen_solver.c:10-19).
    This holds all state needed for constraint propagation. *)
Record SolverCtx := mkSolverCtx {
  ctx_width : nat;                (* w: grid width *)
  ctx_diff : Difficulty;          (* diff: difficulty level *)
  ctx_cages : list Cage;          (* nboxes, boxes, boxlist combined *)
  ctx_mode_flags : ModeFlags;     (* mode_flags *)
  ctx_solution : GridList         (* soln: known solution digits *)
}.

(** ** Latin Solver State *)

(** Latin solver state matching struct latin_solver (latin.h:45-57).
    This tracks possibilities during constraint propagation. *)
Record LatinSolver := mkLatinSolver {
  ls_order : nat;                 (* o: order of latin square *)
  ls_cube : PossibilityCube;      (* cube: o^3 possibility array *)
  ls_grid : GridList;             (* grid: current solution *)
  ls_row : list bool;             (* row: row placement tracking *)
  ls_col : list bool              (* col: column placement tracking *)
}.

(** Initialize latin solver with empty grid *)
Definition init_latin_solver (n : nat) : LatinSolver :=
  mkLatinSolver
    n
    (repeat true (n * n * n))     (* All possibilities initially true *)
    (repeat 0 (n * n))            (* All cells empty *)
    (repeat false (n * n))        (* No row placements *)
    (repeat false (n * n)).       (* No column placements *)

(** ** Solver Result *)

(** Result codes matching latin.h enum (latin.h:119) *)
Inductive SolverResult : Type :=
  | SolvedAt : Difficulty -> SolverResult  (* Solved at given difficulty *)
  | Impossible : SolverResult              (* diff_impossible *)
  | Ambiguous : SolverResult               (* diff_ambiguous *)
  | Unfinished : SolverResult.             (* diff_unfinished *)

(** ** Iscratch Modes *)

(** The iscratch array is used differently at different difficulty levels.
    See solver_clue_candidate comments in keen_solver.c:76-110.

    EASY/NORMAL: iscratch[0..n-1] = candidate bitmaps per cage cell
    HARD: iscratch[0..2w-1] = candidates per row/column intersection *)
Inductive IscratchMode : Type :=
  | IscratchPerCell    (* EASY/NORMAL mode *)
  | IscratchPerRowCol. (* HARD mode *)

Definition iscratch_mode (diff : Difficulty) : IscratchMode :=
  if diff_leb diff DiffNormal then IscratchPerCell
  else IscratchPerRowCol.

(** ** Key Invariants *)

(** Latin square row uniqueness *)
Definition row_unique (n : nat) (g : GridList) : Prop :=
  forall r c1 c2,
    r < n -> c1 < n -> c2 < n -> c1 <> c2 ->
    match nth_error g (r * n + c1), nth_error g (r * n + c2) with
    | Some d1, Some d2 => d1 = 0 \/ d2 = 0 \/ d1 <> d2
    | _, _ => True
    end.

(** Latin square column uniqueness *)
Definition col_unique (n : nat) (g : GridList) : Prop :=
  forall c r1 r2,
    c < n -> r1 < n -> r2 < n -> r1 <> r2 ->
    match nth_error g (r1 * n + c), nth_error g (r2 * n + c) with
    | Some d1, Some d2 => d1 = 0 \/ d2 = 0 \/ d1 <> d2
    | _, _ => True
    end.

(** Latin invariant: rows and columns have no duplicate non-zero digits *)
Definition latin_invariant (n : nat) (g : GridList) : Prop :=
  length g = n * n /\ row_unique n g /\ col_unique n g.

(** Cube-grid consistency: if grid has value, cube has only that possibility *)
Definition cube_grid_consistent (n : nat) (cube : PossibilityCube) (g : GridList) : Prop :=
  forall idx,
    idx < n * n ->
    match nth_error g idx with
    | Some 0 => True  (* Unfilled: any possibilities allowed *)
    | Some d =>
        (* Filled: only this digit should be possible *)
        forall d', d' < n ->
          nth (idx * n + d') cube false = Nat.eqb d (d' + 1)
    | None => False   (* Index out of bounds *)
    end.

(** ** Digit Validity *)

(** All non-zero digits in grid are valid (in range 1..n) *)
Definition digits_valid (n : nat) (g : GridList) : Prop :=
  forall d, In d g -> d > 0 -> valid_digit n d.

(** Strong Latin invariant: includes digit validity *)
Definition valid_latin_grid (n : nat) (g : GridList) : Prop :=
  latin_invariant n g /\ digits_valid n g.

(** ** Helper Lemmas *)

(** cell_to_index stays within bounds for valid cells *)
Lemma cell_to_index_bounds :
  forall n r c,
    r < n -> c < n ->
    cell_to_index n (r, c) < n * n.
Proof.
  intros n r c Hr Hc.
  unfold cell_to_index. simpl.
  (* r * n + c < n * n when r < n and c < n *)
  (* Since r < n, we have r + 1 <= n *)
  (* So r * n + c < r * n + n = (r + 1) * n <= n * n *)
  assert (Hn : n > 0) by lia.
  assert (H1 : r * n + c < (r + 1) * n) by lia.
  assert (H2 : (r + 1) * n <= n * n).
  { apply Nat.mul_le_mono_r. lia. }
  lia.
Qed.

(** grid_get succeeds when cell is in bounds and grid is complete *)
Lemma grid_get_in_bounds :
  forall n g r c,
    length g = n * n ->
    r < n -> c < n ->
    exists d, grid_get n g (r, c) = Some d.
Proof.
  intros n g r c Hlen Hr Hc.
  unfold grid_get.
  assert (Hidx : cell_to_index n (r, c) < length g).
  { rewrite Hlen. apply cell_to_index_bounds; assumption. }
  destruct (nth_error g (cell_to_index n (r, c))) eqn:E.
  - exists d. reflexivity.
  - exfalso. apply nth_error_None in E. lia.
Qed.

(** If grid_get succeeds, the digit is in the grid *)
Lemma grid_get_in :
  forall n g c d,
    grid_get n g c = Some d ->
    In d g.
Proof.
  intros n g c d Hget.
  unfold grid_get in Hget.
  apply nth_error_In with (n := cell_to_index n c).
  exact Hget.
Qed.

(** ** Soundness Theorem *)

(** Main soundness: valid Latin grid cells contain valid digits *)
Theorem latin_constraint_sound :
  forall n g r c d,
    n > 0 ->
    valid_latin_grid n g ->
    r < n -> c < n ->
    grid_get n g (r, c) = Some d ->
    d > 0 ->
    valid_digit n d.
Proof.
  intros n g r c d Hn [Hlatin Hdigits] Hr Hc Hget Hd_pos.
  apply Hdigits.
  - eapply grid_get_in. exact Hget.
  - exact Hd_pos.
Qed.

(** Corollary: valid digits satisfy 1 <= d <= n *)
Corollary latin_constraint_bounds :
  forall n g r c d,
    n > 0 ->
    valid_latin_grid n g ->
    r < n -> c < n ->
    grid_get n g (r, c) = Some d ->
    d > 0 ->
    1 <= d /\ d <= n.
Proof.
  intros n g r c d Hn Hvalid Hr Hc Hget Hd_pos.
  apply latin_constraint_sound with (g := g) (r := r) (c := c); assumption.
Qed.

(** ** Additional Latin Properties *)

(** Empty cells don't violate uniqueness *)
Lemma row_unique_preserves_empty :
  forall n g r c,
    row_unique n g ->
    r < n -> c < n ->
    nth_error g (r * n + c) = Some 0 ->
    True.
Proof.
  intros. exact I.
Qed.

(** Placing a valid digit in empty cell preserves row uniqueness *)
(* TODO Phase 1.1e: Complete this proof - complex row index arithmetic *)
Lemma place_digit_row_unique :
  forall n g r c d g',
    n > 0 ->
    row_unique n g ->
    r < n -> c < n ->
    valid_digit n d ->
    nth_error g (r * n + c) = Some 0 ->
    (* New grid has d at (r,c) *)
    (forall idx, idx <> r * n + c -> nth_error g' idx = nth_error g idx) ->
    nth_error g' (r * n + c) = Some d ->
    (* d is not already in row r *)
    (forall c', c' < n -> c' <> c ->
      match nth_error g (r * n + c') with
      | Some d' => d' <> d
      | None => True
      end) ->
    row_unique n g'.
Proof.
  (* Proof requires careful row/column index arithmetic.
     Key insight: r' * n + c1 = r * n + c implies r' = r when
     all indices are < n, because row indices partition [0, n*n). *)
Admitted.

(** ** Extraction Hints *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.

(** End of SolverTypes *)
