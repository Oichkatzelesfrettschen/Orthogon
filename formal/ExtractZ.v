(**
 * ExtractZ.v: Z-based extraction for KeenKenning
 *
 * Uses Z integers (binary representation) for O(log n) extraction
 * of large numbers, avoiding the O(n) unary successor chains.
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import ZArith.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlZInt ExtrOcamlNatInt.

From KeenKenning Require Import LatinBoundsZ.

(** * Extraction *)

Extraction "latin_z.ml"
  (* Factorial *)
  fact_nat
  fact_z

  (* Latin square counts *)
  latin_count_z
  reduced_count_z
  solution_space_z

  (* Combinatorics *)
  stirling2
  bell_z

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
  MODE_BITWISE.
