(**
 * latin_production.ml: Hand-optimized Latin square bounds
 *
 * This module provides efficient implementations derived from
 * formally verified Rocq specifications. The algorithms are
 * verified in LatinBoundsZ.v and LatinEnum.v.
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

(** {1 Factorial} *)

let rec fact n =
  if n <= 1 then 1
  else n * fact (n - 1)

(** {1 Latin Square Enumeration (OEIS A002860)} *)

(** Reduced Latin square counts (OEIS A000315) *)
let reduced_count = function
  | 1 -> 1 | 2 -> 1 | 3 -> 1 | 4 -> 4
  | 5 -> 56 | 6 -> 9408 | 7 -> 16942080
  | _ -> 0

(** Total Latin squares: L(n) = n! * (n-1)! * R(n) *)
let latin_count n =
  if n <= 0 then 0
  else fact n * fact (n - 1) * reduced_count n

(** {1 Stirling Numbers of Second Kind} *)

(** S(n,k) = ways to partition n elements into k non-empty subsets *)
let rec stirling2 n k =
  match (n, k) with
  | (0, 0) -> 1
  | (0, _) -> 0
  | (_, 0) -> 0
  | (n', k') -> k * stirling2 (n' - 1) k + stirling2 (n' - 1) (k' - 1)

(** {1 Bell Numbers} *)

(** B(n) = total partitions of n elements *)
let bell n =
  if n = 0 then 1
  else
    let rec sum_stirling k acc =
      if k < 0 then acc
      else sum_stirling (k - 1) (acc + stirling2 n k)
    in sum_stirling n 0

(** {1 Cage Ambiguity Analysis} *)

(** Maximum solutions for standard operations (+, -, ×, ÷) *)
let max_ambiguity_standard n cage_size =
  match cage_size with
  | 1 -> 1
  | 2 -> max 0 (n - 1)
  | _ -> fact cage_size

(** Maximum solutions for bitwise XOR (higher ambiguity) *)
let max_ambiguity_bitwise n cage_size =
  match cage_size with
  | 1 -> 1
  | 2 -> n
  | _ ->
    let rec pow b e acc =
      if e <= 0 then acc else pow b (e - 1) (acc * b)
    in pow n cage_size 1

(** {1 Mode Flags (matching C header keen.h)} *)

let mode_standard       = 0x0000
let mode_multiplication = 0x0001
let mode_mystery        = 0x0002
let mode_zero_inclusive = 0x0004
let mode_negative       = 0x0008
let mode_exponent       = 0x0010
let mode_modular        = 0x0020
let mode_killer         = 0x0040
let mode_hint           = 0x0080
let mode_adaptive       = 0x0100
let mode_story          = 0x0200
let mode_bitwise        = 0x0800

(** {1 Auto-Upgrade Rules for 3x3 Grids} *)

(** Automatically add constraint modes for small grids with high difficulty *)
let auto_upgrade_modes n diff =
  if n <> 3 then 0
  else if diff < 2 then 0
  else if diff = 2 then mode_killer
  else if diff = 3 then mode_killer lor mode_bitwise
  else mode_killer lor mode_bitwise lor mode_modular

(** {1 Solution Space} *)

let solution_space n = latin_count n
