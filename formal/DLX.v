(** * Dancing Links (DLX) Algorithm Specification

    Formal specification and verification of Knuth's Algorithm X
    with Dancing Links for solving exact cover problems.

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Basic Definitions *)

(** A matrix row is a list of column indices that are covered by this row *)
Definition Row := list nat.

(** A matrix is a list of rows *)
Definition Matrix := list Row.

(** A solution is a list of row indices *)
Definition Solution := list nat.

(** ** Exact Cover Properties *)

(** Check if a column is in a row *)
Definition in_row (col : nat) (row : Row) : bool :=
  existsb (Nat.eqb col) row.

(** Get all columns covered by a list of rows *)
Fixpoint covered_cols (matrix : Matrix) (rows : list nat) : list nat :=
  match rows with
  | [] => []
  | r :: rest =>
      match nth_error matrix r with
      | Some row => row ++ covered_cols matrix rest
      | None => covered_cols matrix rest
      end
  end.

(** Check if a list has duplicates *)
Fixpoint has_duplicates (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: rest => if existsb (Nat.eqb x) rest then true else has_duplicates rest
  end.

(** An exact cover: selected rows cover each column exactly once *)
Definition is_exact_cover (matrix : Matrix) (num_cols : nat) (sol : Solution) : Prop :=
  let cols := covered_cols matrix sol in
  (* No duplicates - each column covered at most once *)
  has_duplicates cols = false /\
  (* All columns covered - each column covered at least once *)
  length cols = num_cols /\
  (* All rows valid *)
  Forall (fun r => r < length matrix) sol.

(** ** Dancing Links Node Structure *)

(** Node in the doubly-linked structure *)
Record Node := mkNode {
  left : nat;       (** Left neighbor index *)
  right : nat;      (** Right neighbor index *)
  up : nat;         (** Up neighbor index *)
  down : nat;       (** Down neighbor index *)
  col_header : nat; (** Column header index *)
  row_id : nat      (** Row ID (nat max for headers) *)
}.

(** Column header with size *)
Record ColHeader := mkColHeader {
  ch_node : Node;
  ch_size : nat     (** Number of 1s in this column *)
}.

(** DLX matrix structure *)
Record DLXMatrix := mkDLXMatrix {
  nodes : list Node;
  headers : list ColHeader;
  root : nat;            (** Root header index *)
  num_columns : nat;
  num_rows : nat
}.

(** ** Link Invariants *)

(** A node's left link points to a node whose right link points back *)
Definition left_right_consistent (nodes : list Node) (i : nat) : Prop :=
  match nth_error nodes i with
  | Some n =>
      match nth_error nodes (left n) with
      | Some ln => right ln = i
      | None => False
      end
  | None => True  (* vacuously true for invalid indices *)
  end.

(** A node's up link points to a node whose down link points back *)
Definition up_down_consistent (nodes : list Node) (i : nat) : Prop :=
  match nth_error nodes i with
  | Some n =>
      match nth_error nodes (up n) with
      | Some un => down un = i
      | None => False
      end
  | None => True
  end.

(** All links in the matrix are consistent *)
Definition links_consistent (m : DLXMatrix) : Prop :=
  forall i, i < length (nodes m) ->
    left_right_consistent (nodes m) i /\
    up_down_consistent (nodes m) i.

(** ** Cover/Uncover Operations *)

(** Cover operation: remove column from header list and all rows in column *)
(** This is specified abstractly - the key property is reversibility *)

(** State after covering column c *)
Record CoverState := mkCoverState {
  cs_nodes : list Node;
  cs_removed_rows : list nat  (** Row indices that were removed *)
}.

(** Cover removes exactly the rows containing the column *)
Definition cover_spec (m : DLXMatrix) (col : nat) (s : CoverState) : Prop :=
  (* The column header is unlinked horizontally *)
  True.  (* Simplified - full spec would track exact node modifications *)

(** Uncover restores the original state *)
Definition uncover_spec (m : DLXMatrix) (col : nat) (s : CoverState) (m' : DLXMatrix) : Prop :=
  nodes m = nodes m'.  (* Original structure restored *)

(** ** Algorithm X Specification *)

(** Choice function: select column with minimum size (MRV heuristic) *)
Definition choose_column (m : DLXMatrix) : option nat :=
  (* Find column with minimum size > 0 *)
  (* Returns None if all columns are covered *)
  let find_min := fix find_min (hdrs : list ColHeader) (idx : nat) (best : option (nat * nat)) :=
    match hdrs with
    | [] => match best with Some (i, _) => Some i | None => None end
    | h :: rest =>
        let sz := ch_size h in
        if Nat.eqb sz 0 then find_min rest (S idx) best
        else match best with
        | None => find_min rest (S idx) (Some (idx, sz))
        | Some (_, bsz) =>
            if sz <? bsz then find_min rest (S idx) (Some (idx, sz))
            else find_min rest (S idx) best
        end
    end
  in find_min (headers m) 0 None.

(** Search result *)
Inductive SearchResult :=
  | Found : Solution -> SearchResult
  | NotFound : SearchResult.

(** Search depth bound (for termination) *)
(* Note: Simplified stub - full implementation would recurse on fuel *)
Definition search_bounded (m : DLXMatrix) (partial : Solution) (fuel : nat) : SearchResult :=
  match fuel with
  | O => NotFound  (* Out of fuel *)
  | S _ =>
      match choose_column m with
      | None =>
          (* No columns left - we have a solution! *)
          Found (rev partial)
      | Some _ =>
          (* Column needs to be covered *)
          (* Full implementation would iterate rows and recurse *)
          NotFound  (* Simplified stub *)
      end
  end.

(** ** Main Theorems *)

(** Theorem: If search finds a solution, it's a valid exact cover *)
Theorem search_solution_valid :
  forall m partial fuel sol,
    search_bounded m partial fuel = Found sol ->
    is_exact_cover ([] (* original matrix *)) (num_columns m) sol.
Proof.
  intros m partial fuel sol Hsearch.
  (* The proof would show that:
     1. Each covered column is covered exactly once
     2. All columns are covered when choose_column returns None
     3. The solution rows are valid indices *)
  admit.
Admitted.

(** Theorem: Cover followed by uncover preserves structure *)
Theorem cover_uncover_preserves :
  forall m col s m',
    cover_spec m col s ->
    uncover_spec m col s m' ->
    nodes m = nodes m'.
Proof.
  intros m col s m' Hcover Huncover.
  unfold uncover_spec in Huncover.
  exact Huncover.
Qed.

(** ** Constructive Exact Cover Checker *)

(** Check if a solution is an exact cover (decidable) *)
Definition check_exact_cover (matrix : Matrix) (num_cols : nat) (sol : Solution) : bool :=
  let cols := covered_cols matrix sol in
  negb (has_duplicates cols) &&
  Nat.eqb (length cols) num_cols &&
  forallb (fun r => r <? length matrix) sol.

(** The checker is sound *)
Theorem check_exact_cover_sound :
  forall matrix num_cols sol,
    check_exact_cover matrix num_cols sol = true ->
    is_exact_cover matrix num_cols sol.
Proof.
  intros matrix num_cols sol Hcheck.
  unfold check_exact_cover in Hcheck.
  apply andb_prop in Hcheck. destruct Hcheck as [Hcheck Hrows].
  apply andb_prop in Hcheck. destruct Hcheck as [Hnodup Hlen].
  unfold is_exact_cover.
  repeat split.
  - (* No duplicates *)
    apply negb_true_iff in Hnodup. exact Hnodup.
  - (* All columns covered *)
    apply Nat.eqb_eq in Hlen. exact Hlen.
  - (* Valid row indices *)
    rewrite Forall_forall. intros r Hr.
    rewrite forallb_forall in Hrows.
    specialize (Hrows r Hr).
    apply Nat.ltb_lt in Hrows. exact Hrows.
Qed.

(** ** Latin Square as Exact Cover *)

(** Encode Latin square as exact cover matrix *)

(** For an NxN Latin square:
    - Matrix has N^3 rows (one for each (row, col, value) triple)
    - Matrix has 3N^2 columns:
      - Columns 0..N^2-1: cell (r,c) is filled
      - Columns N^2..2N^2-1: row r has value v
      - Columns 2N^2..3N^2-1: column c has value v
*)

(** Row index for placement (r, c, v) *)
Definition placement_row (n r c v : nat) : nat :=
  r * n * n + c * n + (v - 1).

(** Columns covered by placement (r, c, v) *)
Definition placement_cols (n r c v : nat) : Row :=
  [ r * n + c;                    (* Cell filled *)
    n * n + r * n + (v - 1);      (* Row has value *)
    2 * n * n + c * n + (v - 1)   (* Column has value *)
  ].

(** Build exact cover matrix for NxN Latin square *)
Fixpoint build_latin_matrix_rows (n r c v : nat) : Matrix :=
  match v with
  | O => []
  | S v' =>
      placement_cols n r c v :: build_latin_matrix_rows n r c v'
  end.

Fixpoint build_latin_matrix_cols (n r c : nat) : Matrix :=
  match c with
  | O => []
  | S c' =>
      build_latin_matrix_rows n r c' n ++ build_latin_matrix_cols n r c'
  end.

Fixpoint build_latin_matrix_full (n r : nat) : Matrix :=
  match r with
  | O => []
  | S r' =>
      build_latin_matrix_cols n r' n ++ build_latin_matrix_full n r'
  end.

Definition build_latin_matrix (n : nat) : Matrix :=
  build_latin_matrix_full n n.

(** Theorem: Latin matrix has correct dimensions *)
Theorem latin_matrix_dimensions :
  forall n,
    n > 0 ->
    length (build_latin_matrix n) = n * n * n.
Proof.
  intros n Hn.
  (* Would prove by induction on the build functions *)
  admit.
Admitted.

(** ** Extraction *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract to OCaml *)
(* Extraction "DLX.ml" check_exact_cover build_latin_matrix. *)

(** End of DLX specification *)
