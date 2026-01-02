(** * Latin Square Exact Cover Specification

    Formal specification for DLX-based Latin square solving.
    This module defines the mathematical properties required
    for correct puzzle generation and solving.

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Grid Definitions *)

(** A cell position in an n×n grid *)
Definition Cell := (nat * nat)%type.

(** A grid assignment: cell -> value (1 to n) *)
Definition Grid (n : nat) := Cell -> option nat.

(** ** Latin Square Properties *)

(** Cell is within grid bounds *)
Definition in_bounds (n : nat) (c : Cell) : Prop :=
  fst c < n /\ snd c < n.

(** Value is valid for grid size n *)
Definition valid_value (n : nat) (v : nat) : Prop :=
  1 <= v /\ v <= n.

(** A grid is complete if all cells have values *)
Definition complete (n : nat) (g : Grid n) : Prop :=
  forall c, in_bounds n c -> exists v, g c = Some v /\ valid_value n v.

(** Row uniqueness: no value repeats in any row *)
Definition row_unique (n : nat) (g : Grid n) : Prop :=
  forall r c1 c2 v,
    c1 < n -> c2 < n -> c1 <> c2 ->
    g (r, c1) = Some v -> g (r, c2) <> Some v.

(** Column uniqueness: no value repeats in any column *)
Definition col_unique (n : nat) (g : Grid n) : Prop :=
  forall c r1 r2 v,
    r1 < n -> r2 < n -> r1 <> r2 ->
    g (r1, c) = Some v -> g (r2, c) <> Some v.

(** A grid is a valid Latin square *)
Definition is_latin_square (n : nat) (g : Grid n) : Prop :=
  n > 0 /\ complete n g /\ row_unique n g /\ col_unique n g.

(** ** Exact Cover Problem *)

(** A subset is a list of elements *)
Definition Subset (U : Type) := list U.

(** A collection is a list of subsets *)
Definition Collection (U : Type) := list (Subset U).

(** Subsets are disjoint *)
Definition disjoint {U : Type} (s1 s2 : Subset U) : Prop :=
  forall x, ~ (In x s1 /\ In x s2).

(** Pairwise disjoint collection *)
Fixpoint pairwise_disjoint {U : Type} (ss : Collection U) : Prop :=
  match ss with
  | [] => True
  | s :: rest =>
      (forall s', In s' rest -> disjoint s s') /\
      pairwise_disjoint rest
  end.

(** Union of all subsets in a collection *)
Definition union_all {U : Type} (ss : Collection U) : list U :=
  concat ss.

(** Exact cover: selected subsets partition the universe *)
Definition exact_cover {U : Type} (universe : Subset U) (ss : Collection U) : Prop :=
  pairwise_disjoint ss /\
  forall x, In x universe <-> In x (union_all ss).

(** ** Latin Square as Exact Cover *)

(** Constraint types for Latin square exact cover encoding *)
Inductive Constraint (n : nat) : Type :=
  | CellFilled : nat -> nat -> Constraint n     (* Cell (r,c) has some value *)
  | RowValue : nat -> nat -> Constraint n       (* Row r has value v *)
  | ColValue : nat -> nat -> Constraint n.      (* Column c has value v *)

Arguments CellFilled {n}.
Arguments RowValue {n}.
Arguments ColValue {n}.

(** A placement: putting value v at cell (r,c) *)
Record Placement := mkPlacement {
  pl_row : nat;
  pl_col : nat;
  pl_val : nat
}.

(** Constraints satisfied by a placement *)
Definition placement_constraints (n : nat) (p : Placement) : list (Constraint n) :=
  [ CellFilled (pl_row p) (pl_col p);
    RowValue (pl_row p) (pl_val p);
    ColValue (pl_col p) (pl_val p) ].

(** Valid placement for grid size n *)
Definition valid_placement (n : nat) (p : Placement) : Prop :=
  pl_row p < n /\ pl_col p < n /\ 1 <= pl_val p /\ pl_val p <= n.

(** All possible placements for an n×n grid *)
Definition all_placements (n : nat) : list Placement :=
  flat_map (fun r =>
    flat_map (fun c =>
      map (fun v => mkPlacement r c v) (seq 1 n)
    ) (seq 0 n)
  ) (seq 0 n).

(** Solution: a list of placements *)
Definition Solution := list Placement.

(** Solution is valid if placements don't conflict *)
Definition valid_solution (n : nat) (sol : Solution) : Prop :=
  (* All placements are valid *)
  Forall (valid_placement n) sol /\
  (* No two placements in same cell *)
  (forall p1 p2, In p1 sol -> In p2 sol -> p1 <> p2 ->
    ~ (pl_row p1 = pl_row p2 /\ pl_col p1 = pl_col p2)) /\
  (* No duplicate values in rows *)
  (forall p1 p2, In p1 sol -> In p2 sol -> p1 <> p2 ->
    pl_row p1 = pl_row p2 -> pl_val p1 <> pl_val p2) /\
  (* No duplicate values in columns *)
  (forall p1 p2, In p1 sol -> In p2 sol -> p1 <> p2 ->
    pl_col p1 = pl_col p2 -> pl_val p1 <> pl_val p2).

(** Complete solution fills all cells *)
Definition complete_solution (n : nat) (sol : Solution) : Prop :=
  length sol = n * n /\
  forall r c, r < n -> c < n ->
    exists p, In p sol /\ pl_row p = r /\ pl_col p = c.

(** ** DLX Algorithm Specification *)

(** Dancing Links node *)
Record DLXNode := mkNode {
  node_left : nat;    (* Index of left neighbor *)
  node_right : nat;   (* Index of right neighbor *)
  node_up : nat;      (* Index of up neighbor *)
  node_down : nat;    (* Index of down neighbor *)
  node_col : nat;     (* Column header index *)
  node_row : nat      (* Row index (-1 for headers) *)
}.

(** DLX state *)
Record DLXState := mkState {
  nodes : list DLXNode;
  header : nat;        (* Root header index *)
  solution : list nat; (* Stack of selected rows *)
  col_sizes : list nat (* Size of each column *)
}.

(** Cover operation specification *)
(** Column col is removed from the active column list *)
Definition cover_removes_column (state state' : DLXState) (col : nat) : Prop :=
  (* Simplified: column not in solution of state' *)
  ~ In col (solution state').

(** Cover/uncover are inverses (axiom for now) *)
Axiom cover_uncover_inverse :
  forall state state' state'' col,
    cover_removes_column state state' col ->
    cover_removes_column state'' state' col ->
    nodes state = nodes state''.

(** DLX search finds exact cover *)
Definition dlx_finds_cover (matrix : list (list bool)) (solution : list nat) : Prop :=
  (* Each column is covered exactly once by the solution *)
  let n_cols := length (hd [] matrix) in
  forall col, col < n_cols ->
    exists! row, In row solution /\
      nth col (nth row matrix []) false = true.

(** ** Cage Constraints (KenKen-specific) *)

(** Arithmetic operations *)
Inductive CageOp : Type :=
  | OpAdd : CageOp
  | OpSub : CageOp
  | OpMul : CageOp
  | OpDiv : CageOp
  | OpXor : CageOp  (* Bitwise mode *)
  | OpMod : CageOp. (* Modular mode *)

(** A cage definition *)
Record Cage := mkCage {
  cage_cells : list Cell;
  cage_op : CageOp;
  cage_target : nat
}.

(** Evaluate cage constraint given cell values *)
Definition eval_cage (n : nat) (cage : Cage) (values : list nat) : option nat :=
  match cage_op cage, values with
  | OpAdd, _ => Some (fold_left Nat.add values 0)
  | OpMul, _ => Some (fold_left Nat.mul values 1)
  | OpSub, [a; b] => Some (if a <=? b then b - a else a - b)
  | OpDiv, [a; b] => if Nat.eqb (a mod b) 0 then Some (a / b)
                     else if Nat.eqb (b mod a) 0 then Some (b / a)
                     else None
  | OpXor, _ => Some (fold_left Nat.lxor values 0)
  | OpMod, _ => Some ((fold_left Nat.add values 0) mod n)
  | _, _ => None
  end.

(** Cage constraint is satisfied *)
Definition cage_satisfied (n : nat) (cage : Cage) (g : Grid n) : Prop :=
  exists values,
    length values = length (cage_cells cage) /\
    (forall i c, nth_error (cage_cells cage) i = Some c ->
      nth_error values i = g c) /\
    eval_cage n cage values = Some (cage_target cage).

(** Killer mode: no repeated digits in cage *)
Definition killer_constraint (n : nat) (cage : Cage) (g : Grid n) : Prop :=
  forall c1 c2 v,
    In c1 (cage_cells cage) ->
    In c2 (cage_cells cage) ->
    c1 <> c2 ->
    g c1 = Some v ->
    g c2 <> Some v.

(** Full puzzle constraint *)
Definition puzzle_valid (n : nat) (cages : list Cage) (g : Grid n) (killer : bool) : Prop :=
  is_latin_square n g /\
  (forall cage, In cage cages -> cage_satisfied n cage g) /\
  (if killer then forall cage, In cage cages -> killer_constraint n cage g
   else True).

(** ** Key Theorems *)

(** Theorem: Valid solution implies Latin square *)
Theorem valid_complete_solution_is_latin :
  forall n sol,
    n > 0 ->
    valid_solution n sol ->
    complete_solution n sol ->
    exists g : Grid n, is_latin_square n g.
Proof.
  intros n sol Hn Hvalid Hcomplete.
  (* Construct grid from placements *)
  exists (fun (cell : Cell) =>
    let '(r, c) := cell in
    match find (fun p =>
      andb (Nat.eqb (pl_row p) r) (Nat.eqb (pl_col p) c)) sol with
    | Some p => Some (pl_val p)
    | None => None
    end).
  unfold is_latin_square.
  repeat split.
  - (* n > 0 *) exact Hn.
  - (* complete *)
    unfold complete. intros [r c] [Hr Hc].
    destruct Hcomplete as [_ Hfill].
    destruct (Hfill r c Hr Hc) as [p [Hin [Hpr Hpc]]].
    (* The find will succeed for this cell *)
    admit. (* Proof that find succeeds and returns valid value *)
  - (* row_unique *)
    unfold row_unique. intros r c1 c2 v Hc1 Hc2 Hneq Hg1.
    (* From valid_solution, no duplicate values in rows *)
    admit.
  - (* col_unique *)
    unfold col_unique. intros c r1 r2 v Hr1 Hr2 Hneq Hg1.
    (* From valid_solution, no duplicate values in columns *)
    admit.
Admitted.

(** Theorem: DLX exact cover solution is valid *)
Theorem dlx_solution_valid :
  forall n matrix solution,
    n > 0 ->
    length matrix = n * n * n ->  (* n^3 rows: n² cells × n values each *)
    dlx_finds_cover matrix solution ->
    exists sol : Solution,
      length sol = n * n /\
      valid_solution n sol.
Proof.
  intros n matrix solution Hn Hlen Hcover.
  (* Solution rows correspond to placements *)
  (* Each selected row encodes a (cell, value) pair *)
  admit.
Admitted.

(** ** Extraction Hints *)

(* Prepare for extraction to OCaml *)
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(** End of specification *)
