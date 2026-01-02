(**
 * ExtractOptimized.v: Optimized OCaml extraction for KeenKenning
 *
 * This module configures extraction to produce efficient OCaml code
 * that can be translated to C or used directly via OCaml-C FFI.
 *
 * Key optimizations:
 * - Native int for nat (bounded, but efficient)
 * - Native bool
 * - Native list operations
 * - Inline small functions
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import Arith Bool List ZArith Lia Nat.
From Stdlib Require Extraction.
From Stdlib Require ExtrOcamlBasic.

From KeenKenning Require Import LatinEnum.
From KeenKenning Require Import Modes.
From KeenKenning Require Import LatinSquare.
From KeenKenning Require Import DLX.
From KeenKenning Require Import SAT.

(** * Extraction Configuration *)

(** Use native int - this is the key optimization.
    We trade off arbitrary precision for efficiency.
    For KenKen (n <= 16), this is safe. *)

Extract Inductive nat => "int"
  ["0" "(fun n -> n + 1)"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

(** Native arithmetic *)
Extract Constant Nat.add => "(+)".
Extract Constant Nat.sub => "(fun n m -> max 0 (n - m))".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.modulo => "(mod)".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.compare =>
  "(fun n m -> if n < m then Lt else if n = m then Eq else Gt)".
Extract Constant Nat.max => "max".
Extract Constant Nat.min => "min".
Extract Constant Nat.pow =>
  "(fun b e -> int_of_float (float_of_int b ** float_of_int e))".

(** Native bool *)
Extract Inductive bool => "bool" ["true" "false"].
Extract Constant Bool.eqb => "(=)".
Extract Constant andb => "(&&)".
Extract Constant orb => "(||)".
Extract Constant negb => "not".

(** Native list *)
Extract Inductive list => "list" ["[]" "(::)"].
Extract Constant List.length => "List.length".
Extract Constant List.app => "(@)".
Extract Constant List.rev => "List.rev".
Extract Constant List.map => "List.map".
Extract Constant List.fold_left => "List.fold_left".
Extract Constant List.fold_right => "(fun f l a -> List.fold_right f a l)".
Extract Constant List.filter => "List.filter".
Extract Constant List.nth => "(fun l n -> List.nth l n)".
Extract Constant List.hd => "(fun d l -> match l with [] -> d | h::_ -> h)".
Extract Constant List.tl => "(fun l -> match l with [] -> [] | _::t -> t)".

(** Native option *)
Extract Inductive option => "option" ["Some" "None"].

(** Native pair *)
Extract Inductive prod => "( * )" ["(,)"].

(** Comparison type *)
Extract Inductive comparison => "int" ["(-1)" "0" "1"].

(** Z integers - use native int (safe for our use case) *)
Extract Inductive Z => "int" ["0" "(fun n -> n)" "(fun n -> -n)"]
  "(fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))".
Extract Constant Z.add => "(+)".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.div => "(/)".
Extract Constant Z.modulo => "(mod)".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "abs".
Extract Constant Z.compare =>
  "(fun x y -> if x < y then Lt else if x = y then Eq else Gt)".
Extract Constant Z.eqb => "(=)".
Extract Constant Z.ltb => "(<)".
Extract Constant Z.leb => "(<=)".
Extract Constant Z.of_nat => "(fun n -> n)".
Extract Constant Z.to_nat => "(fun z -> max 0 z)".

(** Bitwise operations *)
Extract Constant Z.land => "(land)".
Extract Constant Z.lor => "(lor)".
Extract Constant Z.lxor => "(lxor)".
Extract Constant Z.shiftl => "(fun n s -> n lsl s)".
Extract Constant Z.shiftr => "(fun n s -> n asr s)".

(** Inline small functions for performance *)
Extraction Inline Nat.add Nat.sub Nat.mul.
Extraction Inline andb orb negb.
Extraction Inline fst snd.

(** * Extraction Commands *)

(** Create main extracted module with all key definitions *)
Extraction "latin_optimized.ml"
  (* LatinEnum exports *)
  fact
  latin_count
  reduced_count
  solution_space
  stirling2
  sum_stirling
  bell
  max_ambiguity_standard
  max_ambiguity_bitwise

  (* Modes exports *)
  GameMode
  mode_to_flags
  Flavor
  mode_available
  classik_modes
  kenning_modes
  MODE_STANDARD
  MODE_MULTIPLICATION
  MODE_MYSTERY
  MODE_ZERO_INCLUSIVE
  MODE_NEGATIVE
  MODE_EXPONENT
  MODE_MODULAR
  MODE_KILLER
  MODE_HINT
  MODE_ADAPTIVE
  MODE_STORY
  MODE_BITWISE

  (* LatinEnum additional *)
  auto_upgrade_modes.
