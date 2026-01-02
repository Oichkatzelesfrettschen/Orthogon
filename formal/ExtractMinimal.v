(**
 * ExtractMinimal.v: Minimal extraction for KeenKenning
 *
 * This module extracts ONLY computational functions that benefit from
 * formal verification. Constants and mode flags should be defined
 * directly in OCaml/C for efficiency.
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import Arith Bool List Nat.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt.

(** * Inline Computational Functions *)

(** Tail-recursive factorial *)
Definition fact_aux (acc n : nat) : nat :=
  (fix go acc n :=
    match n with
    | 0 => acc
    | S m => go (n * acc) m
    end) acc n.

Definition fact (n : nat) : nat := fact_aux 1 n.

(** Stirling numbers - verified recursive definition *)
Fixpoint stirling2 (n k : nat) : nat :=
  match n, k with
  | 0, 0 => 1
  | 0, S _ => 0
  | S _, 0 => 0
  | S n', S k' => S k' * stirling2 n' (S k') + stirling2 n' k'
  end.

(** Sum of Stirling numbers *)
Fixpoint sum_stirling (n k : nat) : nat :=
  match k with
  | 0 => stirling2 n 0
  | S k' => stirling2 n k + sum_stirling n k'
  end.

(** Bell numbers *)
Definition bell (n : nat) : nat :=
  match n with
  | 0 => 1
  | S _ => sum_stirling n n
  end.

(** Maximum ambiguity for standard operations *)
Definition max_ambiguity_std (n cage_size : nat) : nat :=
  match cage_size with
  | 1 => 1
  | 2 => n - 1
  | _ => fact cage_size
  end.

(** Maximum ambiguity for bitwise operations *)
Definition max_ambiguity_bit (n cage_size : nat) : nat :=
  match cage_size with
  | 1 => 1
  | 2 => n
  | _ => Nat.pow n cage_size
  end.

(** Power function extraction *)
Extract Constant Nat.pow => "(fun b e ->
  let rec pow_aux acc b e =
    if e = 0 then acc
    else pow_aux (acc * b) b (e - 1)
  in pow_aux 1 b e)".

(** * Extraction *)

Extraction "latin_minimal.ml"
  fact
  stirling2
  sum_stirling
  bell
  max_ambiguity_std
  max_ambiguity_bit.
