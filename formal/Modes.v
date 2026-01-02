(**
 * Modes.v: Formal specification of KeenKenning game modes and constraints
 *
 * This module formally verifies:
 * - Game mode bit flag correctness
 * - Mode availability per flavor (Classik vs Kenning)
 * - Grid size constraints per flavor
 * - Difficulty level constraints
 * - Mode/size/difficulty compatibility
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Import ListNotations.

(** * Game Mode Definitions *)

(** Mode flags as used in C layer (keen.h) *)
Definition MODE_STANDARD          := 0.
Definition MODE_MULTIPLICATION    := 1.      (* 0x01 *)
Definition MODE_MYSTERY           := 2.      (* 0x02 *)
Definition MODE_ZERO_INCLUSIVE    := 4.      (* 0x04 *)
Definition MODE_NEGATIVE          := 8.      (* 0x08 *)
Definition MODE_EXPONENT          := 16.     (* 0x10 *)
Definition MODE_MODULAR           := 32.     (* 0x20 *)
Definition MODE_KILLER            := 64.     (* 0x40 *)
Definition MODE_HINT              := 128.    (* 0x80 *)
Definition MODE_ADAPTIVE          := 256.    (* 0x100 *)
Definition MODE_STORY             := 512.    (* 0x200 *)
Definition MODE_BITWISE           := 2048.   (* 0x800 *)

(** Game mode enumeration *)
Inductive GameMode : Type :=
  | Standard
  | MultiplicationOnly
  | Mystery
  | ZeroInclusive
  | NegativeNumbers
  | Exponent
  | Modular
  | Killer
  | HintMode
  | Adaptive
  | Story
  | Bitwise
  | Retro8Bit.  (* UI-only, same flags as Standard *)

(** Map mode to C flags *)
Definition mode_to_flags (m : GameMode) : nat :=
  match m with
  | Standard          => MODE_STANDARD
  | MultiplicationOnly => MODE_MULTIPLICATION
  | Mystery           => MODE_MYSTERY
  | ZeroInclusive     => MODE_ZERO_INCLUSIVE
  | NegativeNumbers   => MODE_NEGATIVE
  | Exponent          => MODE_EXPONENT
  | Modular           => MODE_MODULAR
  | Killer            => MODE_KILLER
  | HintMode          => MODE_HINT
  | Adaptive          => MODE_ADAPTIVE
  | Story             => MODE_STORY
  | Bitwise           => MODE_BITWISE
  | Retro8Bit         => MODE_STANDARD  (* UI-only, same as Standard *)
  end.

(** * Flavor Definitions *)

Inductive Flavor : Type :=
  | Classik   (* Classic experience: limited modes, 3-9 grid sizes *)
  | Kenning.  (* Full feature set: all modes, 3-16 grid sizes *)

(** Classik flavor only supports Standard and Retro8Bit *)
Definition classik_modes : list GameMode :=
  [Standard; Retro8Bit].

(** Kenning flavor supports all modes *)
Definition kenning_modes : list GameMode :=
  [Standard; MultiplicationOnly; Mystery; ZeroInclusive;
   NegativeNumbers; Exponent; Modular; Killer;
   HintMode; Adaptive; Story; Bitwise; Retro8Bit].

(** Check if mode is available in flavor *)
Definition mode_available (f : Flavor) (m : GameMode) : bool :=
  match f with
  | Classik => match m with
               | Standard | Retro8Bit => true
               | _ => false
               end
  | Kenning => true  (* All modes available *)
  end.

(** * Grid Size Constraints *)

Definition MIN_GRID_SIZE_CLASSIK := 3.
Definition MAX_GRID_SIZE_CLASSIK := 9.
Definition MIN_GRID_SIZE_KENNING := 3.
Definition MAX_GRID_SIZE_KENNING := 16.

(** Maximum grid size for extended modes (Zero/Negative/Modular/Exponent) *)
Definition MAX_EXTENDED_MODE_SIZE := 9.

(** Grid size bounds per flavor *)
Definition min_grid_size (f : Flavor) : nat :=
  match f with
  | Classik => MIN_GRID_SIZE_CLASSIK
  | Kenning => MIN_GRID_SIZE_KENNING
  end.

Definition max_grid_size (f : Flavor) : nat :=
  match f with
  | Classik => MAX_GRID_SIZE_CLASSIK
  | Kenning => MAX_GRID_SIZE_KENNING
  end.

(** Check if grid size is valid for flavor *)
Definition valid_grid_size (f : Flavor) (n : nat) : bool :=
  andb (min_grid_size f <=? n) (n <=? max_grid_size f).

(** Extended modes have size limits *)
Definition is_extended_mode (m : GameMode) : bool :=
  match m with
  | ZeroInclusive | NegativeNumbers | Modular | Exponent => true
  | _ => false
  end.

(** Check if mode/size combination is valid *)
Definition valid_mode_size (m : GameMode) (n : nat) : bool :=
  if is_extended_mode m then n <=? MAX_EXTENDED_MODE_SIZE
  else true.

(** * Difficulty Definitions *)

(** 7 difficulty levels matching keen.c DIFFLIST *)
Inductive Difficulty : Type :=
  | Easy            (* Level 0 *)
  | Normal          (* Level 1 *)
  | Hard            (* Level 2 *)
  | Extreme         (* Level 3 *)
  | Unreasonable    (* Level 4 *)
  | Ludicrous       (* Level 5 *)
  | Incomprehensible. (* Level 6 *)

Definition difficulty_to_level (d : Difficulty) : nat :=
  match d with
  | Easy            => 0
  | Normal          => 1
  | Hard            => 2
  | Extreme         => 3
  | Unreasonable    => 4
  | Ludicrous       => 5
  | Incomprehensible => 6
  end.

Definition level_to_difficulty (n : nat) : option Difficulty :=
  match n with
  | 0 => Some Easy
  | 1 => Some Normal
  | 2 => Some Hard
  | 3 => Some Extreme
  | 4 => Some Unreasonable
  | 5 => Some Ludicrous
  | 6 => Some Incomprehensible
  | _ => None
  end.

(** All difficulties are valid for all grid sizes after Phase 2 auto-upgrade *)
Definition valid_difficulty (_ : nat) (_ : Difficulty) : bool := true.

(** * 3x3 Auto Mode Upgrade (Phase 2 implementation)
    For 3x3 grids at HARD+ difficulty, modes are automatically upgraded:
    - HARD: Auto-enables KILLER
    - EXTREME: Auto-enables KILLER + BITWISE
    - UNREASONABLE+: Auto-enables KILLER + BITWISE + MODULAR
*)

Definition auto_upgrade_flags (grid_size : nat) (d : Difficulty) (base_flags : nat) : nat :=
  if negb (grid_size =? 3) then base_flags
  else
    let level := difficulty_to_level d in
    if level <? 2 then base_flags  (* Easy/Normal: no upgrade *)
    else if level =? 2 then base_flags + MODE_KILLER  (* Hard: +KILLER *)
    else if level =? 3 then base_flags + MODE_KILLER + MODE_BITWISE  (* Extreme *)
    else base_flags + MODE_KILLER + MODE_BITWISE + MODE_MODULAR.  (* Unreasonable+ *)

(** * Validation Theorems *)

(** Mode flags are powers of 2 (single bit set) or zero *)
Theorem mode_flags_valid : forall m : GameMode,
  let flags := mode_to_flags m in
  flags = 0 \/ exists k, flags = 2^k.
Proof.
  intros m. simpl.
  destruct m; simpl.
  - left. reflexivity.  (* Standard = 0 *)
  - right. exists 0. reflexivity.  (* 2^0 = 1 *)
  - right. exists 1. reflexivity.  (* 2^1 = 2 *)
  - right. exists 2. reflexivity.  (* 2^2 = 4 *)
  - right. exists 3. reflexivity.  (* 2^3 = 8 *)
  - right. exists 4. reflexivity.  (* 2^4 = 16 *)
  - right. exists 5. reflexivity.  (* 2^5 = 32 *)
  - right. exists 6. reflexivity.  (* 2^6 = 64 *)
  - right. exists 7. reflexivity.  (* 2^7 = 128 *)
  - right. exists 8. reflexivity.  (* 2^8 = 256 *)
  - right. exists 9. reflexivity.  (* 2^9 = 512 *)
  - right. exists 11. reflexivity. (* 2^11 = 2048 *)
  - left. reflexivity.  (* Retro8Bit = 0 *)
Qed.

(** Classik modes are subset of Kenning modes *)
Theorem classik_subset_kenning : forall m : GameMode,
  mode_available Classik m = true -> mode_available Kenning m = true.
Proof.
  intros m H. simpl. reflexivity.
Qed.

(** Grid size bounds are consistent *)
Theorem grid_bounds_consistent : forall f : Flavor,
  min_grid_size f <= max_grid_size f.
Proof.
  intros f. destruct f; simpl.
  - (* Classik: 3 <= 9 *) repeat constructor.
  - (* Kenning: 3 <= 16 *) repeat constructor.
Qed.

(** Difficulty levels are sequential 0-6 *)
Theorem difficulty_levels_sequential : forall d : Difficulty,
  difficulty_to_level d <= 6.
Proof.
  intros d. destruct d; simpl; repeat constructor.
Qed.

(** Level-to-difficulty roundtrip *)
Theorem difficulty_roundtrip : forall d : Difficulty,
  level_to_difficulty (difficulty_to_level d) = Some d.
Proof.
  intros d. destruct d; reflexivity.
Qed.

(** Auto-upgrade preserves base flags *)
Theorem auto_upgrade_preserves_base : forall n d flags,
  n <> 3 -> auto_upgrade_flags n d flags = flags.
Proof.
  intros n d flags H.
  unfold auto_upgrade_flags.
  destruct (n =? 3) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - simpl. reflexivity.
Qed.

(** Auto-upgrade adds constraint modes for 3x3 Hard+ *)
Theorem auto_upgrade_3x3_hard : forall flags,
  auto_upgrade_flags 3 Hard flags = flags + MODE_KILLER.
Proof.
  intros flags. unfold auto_upgrade_flags. simpl. reflexivity.
Qed.

Theorem auto_upgrade_3x3_extreme : forall flags,
  auto_upgrade_flags 3 Extreme flags = flags + MODE_KILLER + MODE_BITWISE.
Proof.
  intros flags. unfold auto_upgrade_flags. simpl. reflexivity.
Qed.

(** * Constants Summary for C Implementation

    Mode flags:
      MODE_STANDARD          = 0x00
      MODE_MULTIPLICATION    = 0x01
      MODE_MYSTERY           = 0x02
      MODE_ZERO_INCLUSIVE    = 0x04
      MODE_NEGATIVE          = 0x08
      MODE_EXPONENT          = 0x10
      MODE_MODULAR           = 0x20
      MODE_KILLER            = 0x40
      MODE_HINT              = 0x80
      MODE_ADAPTIVE          = 0x100
      MODE_STORY             = 0x200
      MODE_BITWISE           = 0x800

    Grid size bounds:
      MIN_GRID_SIZE_CLASSIK  = 3
      MAX_GRID_SIZE_CLASSIK  = 9
      MIN_GRID_SIZE_KENNING  = 3
      MAX_GRID_SIZE_KENNING  = 16
      MAX_EXTENDED_MODE_SIZE = 9
*)
