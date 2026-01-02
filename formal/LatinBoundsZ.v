(**
 * LatinBoundsZ.v: Z-based Latin square bounds for efficient extraction
 *
 * Uses Coq's Z type (binary integers) instead of nat for:
 * - O(log n) representation of large numbers
 * - Efficient extraction to OCaml int
 * - Avoids unary successor chains
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(** * Factorial using Z *)

Fixpoint fact_pos (p : positive) : Z :=
  match p with
  | xH => 1
  | xO p' => let f := fact_pos p' in
             let n := Z.pos p in
             f * (Z.pos (Pos.pred_double p') + 1) * n
  | xI p' => let f := fact_pos p' in
             let n := Z.pos p in
             f * (Z.pos (xO p')) * n
  end.

(** Factorial via nat fuel then convert *)
Fixpoint fact_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S m => Z.of_nat n * fact_nat m
  end.

Definition fact_z (n : Z) : Z :=
  match n with
  | Z0 => 1
  | Zpos p => fact_nat (Pos.to_nat p)
  | Zneg _ => 0
  end.

(** * OEIS A000315: Reduced Latin Squares *)

Definition reduced_count_z (n : Z) : Z :=
  match n with
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 4
  | 5 => 56
  | 6 => 9408
  | _ => 0
  end.

(** * OEIS A002860: Latin Square Count *)

(** Using the relationship L(n) = n! * (n-1)! * R(n) *)
Definition latin_count_z (n : Z) : Z :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 12
  | 4 => 576
  | _ =>
    if n >? 0 then
      fact_z n * fact_z (n - 1) * reduced_count_z n
    else 0
  end.

(** * Stirling Numbers of Second Kind *)

(** S(n,k) = k*S(n-1,k) + S(n-1,k-1) *)
Fixpoint stirling2_z (fuel n k : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
    match n, k with
    | O, O => 1
    | O, S _ => 0
    | S _, O => 0
    | S n', S k' =>
      Z.of_nat (S k') * stirling2_z fuel' n' (S k') +
      stirling2_z fuel' n' k'
    end
  end.

Definition stirling2 (n k : nat) : Z :=
  stirling2_z (n + 1) n k.

(** * Bell Numbers *)

Fixpoint sum_stirling_z (fuel n k : nat) : Z :=
  match k with
  | O => stirling2_z fuel n 0
  | S k' => stirling2_z fuel n k + sum_stirling_z fuel n k'
  end.

Definition bell_z (n : nat) : Z :=
  match n with
  | O => 1
  | S _ => sum_stirling_z (n + 1) n n
  end.

(** * Mode Flags (as Z constants) *)

Definition MODE_STANDARD : Z := 0.
Definition MODE_MULTIPLICATION : Z := 1.
Definition MODE_MYSTERY : Z := 2.
Definition MODE_ZERO_INCLUSIVE : Z := 4.
Definition MODE_NEGATIVE : Z := 8.
Definition MODE_EXPONENT : Z := 16.
Definition MODE_MODULAR : Z := 32.
Definition MODE_KILLER : Z := 64.
Definition MODE_HINT : Z := 128.
Definition MODE_ADAPTIVE : Z := 256.
Definition MODE_STORY : Z := 512.
Definition MODE_BITWISE : Z := 2048.

(** * Solution Space *)

Definition solution_space_z (n : Z) : Z := latin_count_z n.

(** * Verification Lemmas *)

Lemma latin_3_correct : latin_count_z 3 = 12.
Proof. reflexivity. Qed.

Lemma latin_4_correct : latin_count_z 4 = 576.
Proof. reflexivity. Qed.

Lemma reduced_6_correct : reduced_count_z 6 = 9408.
Proof. reflexivity. Qed.

(** Verify 5! = 120 *)
Lemma fact_5_correct : fact_z 5 = 120.
Proof. reflexivity. Qed.

(** Verify 6! = 720 *)
Lemma fact_6_correct : fact_z 6 = 720.
Proof. reflexivity. Qed.
