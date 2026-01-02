(**
 * ExtractClean.v: Clean OCaml extraction for KeenKenning
 *
 * This module produces efficient OCaml code by:
 * - Using LatinBoundsClean (no large literals)
 * - Mapping nat to native int
 * - Mapping bool, list, option to native types
 * - Inlining small functions
 *
 * The extracted code can be compiled with ocamlopt for native performance
 * or transpiled to C for JNI integration.
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import Arith Bool List Nat.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlNatInt.

(** Import clean module (no large literals) *)
From KeenKenning Require Import LatinBoundsClean.

(** * Supplementary Native Extraction *)

(** ExtrOcamlNatInt handles nat -> int and basic arithmetic *)
(** We add missing operations *)

Extract Constant Nat.pow => "(fun b e ->
  let rec pow_aux acc b e =
    if e = 0 then acc
    else pow_aux (acc * b) b (e - 1)
  in pow_aux 1 b e)".

(** * Main Extraction *)

Extraction "latin_clean.ml"
  (* Arithmetic *)
  fact

  (* Latin square bounds *)
  latin_count
  latin_count_compute
  reduced_count
  solution_space

  (* Combinatorics *)
  stirling2
  sum_stirling
  bell

  (* Ambiguity analysis *)
  max_ambiguity_standard
  max_ambiguity_bitwise

  (* Mode flags *)
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

  (* Auto-upgrade *)
  auto_upgrade_modes.
