(**
 * Extract.v: OCaml extraction of verified Latin square bounds
 *
 * Extracts key functions and theorems to OCaml for integration with C layer.
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import Arith Bool List Lia Nat ZArith.
From Stdlib Require Extraction.
From Stdlib Require ExtrOcamlBasic.
From Stdlib Require ExtrOcamlNatInt.

From KeenKenning Require Import LatinEnum.
From KeenKenning Require Import Modes.

(** Use OCaml native integers for efficiency *)
Extract Inductive nat => "int"
  ["0" "succ"]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive list => "list" ["[]" "(::)"].

(** Extract key functions *)
Extraction "latin_bounds.ml"
  latin_count
  reduced_count
  fact
  solution_space
  max_ambiguity_standard
  max_ambiguity_bitwise
  auto_upgrade_modes
  stirling2
  sum_stirling
  bell
  MODE_KILLER
  MODE_BITWISE
  MODE_MODULAR.
