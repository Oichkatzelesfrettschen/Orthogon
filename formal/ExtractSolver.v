(** * ExtractSolver: OCaml Extraction for KenKen Solver

    Extracts the verified solver and generator specifications to OCaml.
    This module configures extraction and exports the key definitions
    needed for integration with the C implementation.

    Extraction order:
    1. SolverTypes - Core type definitions
    2. DSF - Disjoint Set Forest (Union-Find)
    3. CageOps - Cage operation evaluation
    4. SolverSpec - Constraint propagation solver
    5. GeneratorSpec - Puzzle generator

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

From KeenKenning Require Import SolverTypes.
From KeenKenning Require Import DSF.
From KeenKenning Require Import CageOps.
From KeenKenning Require Import SolverSpec.
From KeenKenning Require Import GeneratorSpec.

(** ** Extraction Configuration *)

(** Set extraction output directory *)
Set Extraction Output Directory "extracted".

(** Use efficient OCaml primitives for basic types *)

(* Extract nat to int with bounds checking *)
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Extract bool to OCaml bool *)
Extract Inductive bool => "bool" [ "true" "false" ].

(* Extract list to OCaml list *)
Extract Inductive list => "list" [ "[]" "(::)" ].

(* Extract option to OCaml option *)
Extract Inductive option => "option" [ "Some" "None" ].

(* Extract prod to OCaml tuple *)
Extract Inductive prod => "(*)" [ "(,)" ].

(* Extract Z to OCaml int *)
Extract Inductive Z => "int" [ "0" "(fun p -> p)" "(fun p -> -p)" ]
  "(fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))".
Extract Constant Z.add => "(+)".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "abs".
Extract Constant Z.eqb => "(=)".
Extract Constant Z.ltb => "(<)".
Extract Constant Z.leb => "(<=)".
Extract Constant Z.lxor => "(lxor)".
Extract Constant Z.of_nat => "(fun n -> n)".
Extract Constant Z.to_nat => "(fun z -> if z < 0 then 0 else z)".

(* Efficient bitwise operations *)
Extract Constant Nat.lxor => "(lxor)".
Extract Constant Nat.land => "(land)".
Extract Constant Nat.lor => "(lor)".
Extract Constant Nat.shiftl => "(fun n k -> n lsl k)".
Extract Constant Nat.shiftr => "(fun n k -> n lsr k)".
Extract Constant Nat.testbit => "(fun n k -> (n lsr k) land 1 = 1)".

(** ** DSF Module Extraction *)

(* Extract DSF types and operations - use fully qualified names *)
Extraction "DSFOps.ml"
  (* Types - DSF.DSF is the type alias *)
  DSF.dsf_init_entry

  (* Operations *)
  DSF.dsf_init
  DSF.dsf_get
  DSF.dsf_set
  DSF.dsf_canonify
  DSF.edsf_canonify
  DSF.dsf_size
  DSF.dsf_merge
  DSF.edsf_merge

  (* Predicates (for testing) *)
  DSF.dsf_is_root
  DSF.dsf_is_inverse
  DSF.dsf_parent_or_size.

(** ** CageOps Module Extraction *)

(* Extract cage operation evaluators - use fully qualified names *)
Extraction "CageOpsEval.ml"
  (* Fold operations *)
  CageOps.fold_add
  CageOps.fold_mul
  CageOps.fold_xor
  CageOps.fold_and
  CageOps.fold_or
  CageOps.fold_gcd
  CageOps.fold_lcm
  CageOps.pow

  (* Evaluators *)
  CageOps.eval_add
  CageOps.eval_mul
  CageOps.eval_sub
  CageOps.eval_div
  CageOps.eval_exp
  CageOps.eval_mod
  CageOps.eval_xor
  CageOps.eval_and
  CageOps.eval_or
  CageOps.eval_gcd
  CageOps.eval_lcm
  CageOps.eval_cage_op

  (* Satisfaction *)
  CageOps.cage_satisfiedb

  (* Classification *)
  CageOps.classify_op.

(** ** SolverSpec Module Extraction *)

(* Extract solver state and operations - use fully qualified names *)
Extraction "SolverSpecOps.ml"
  (* State management *)
  SolverSpec.SolverState
  SolverSpec.mkSolverState
  SolverSpec.ss_cube
  SolverSpec.ss_grid
  SolverSpec.ss_changed
  SolverSpec.init_solver_state

  (* Cube operations *)
  SolverSpec.cube_set
  SolverSpec.cube_eliminate
  SolverSpec.cube_possible
  SolverSpec.cell_possibilities
  SolverSpec.cell_unique_digit

  (* Constraint propagation *)
  SolverSpec.propagate_row
  SolverSpec.propagate_col
  SolverSpec.place_digit
  SolverSpec.PlaceResult
  SolverSpec.mkPlaceResult

  (* Solver loop *)
  SolverSpec.elimination_pass
  SolverSpec.solver_loop
  SolverSpec.check_solver_result

  (* Validity checks *)
  SolverSpec.grid_complete_check

  (* Configuration *)
  SolverSpec.SolverConfig
  SolverSpec.mkSolverConfig
  SolverSpec.config_easy
  SolverSpec.config_normal
  SolverSpec.config_hard
  SolverSpec.config_extreme
  SolverSpec.config_unreasonable.

(** ** GeneratorSpec Module Extraction *)

(* Extract generator definitions - use fully qualified names *)
Extraction "GeneratorSpecOps.ml"
  (* Generator state *)
  GeneratorSpec.GenState
  GeneratorSpec.mkGenState
  GeneratorSpec.gs_grid
  GeneratorSpec.gs_dsf
  GeneratorSpec.gs_singletons
  GeneratorSpec.gs_clues

  (* Generator config *)
  GeneratorSpec.GenConfig
  GeneratorSpec.mkGenConfig
  GeneratorSpec.gc_width
  GeneratorSpec.gc_diff
  GeneratorSpec.gc_mode_flags
  GeneratorSpec.gc_maxblk

  (* Generator output *)
  GeneratorSpec.GeneratorOutput
  GeneratorSpec.mkGeneratorOutput
  GeneratorSpec.go_grid
  GeneratorSpec.go_cages
  GeneratorSpec.go_width

  (* Operation flags *)
  GeneratorSpec.F_ADD
  GeneratorSpec.F_SUB
  GeneratorSpec.F_MUL
  GeneratorSpec.F_DIV
  GeneratorSpec.F_EXP
  GeneratorSpec.F_MOD
  GeneratorSpec.F_GCD
  GeneratorSpec.F_LCM
  GeneratorSpec.F_XOR
  GeneratorSpec.valid_clue_flags

  (* Grid size complexity *)
  GeneratorSpec.MIN_GRID_SIZE
  GeneratorSpec.MAX_GRID_SIZE
  GeneratorSpec.GridCategory
  GeneratorSpec.classify_grid_size
  GeneratorSpec.solution_space

  (* Difficulty theory *)
  GeneratorSpec.technique_level
  GeneratorSpec.min_difficulty_for_size
  GeneratorSpec.max_difficulty_for_size
  GeneratorSpec.estimated_cage_count
  GeneratorSpec.average_cage_size

  (* Retry logic *)
  GeneratorSpec.retry_budget

  (* Mode transformations *)
  GeneratorSpec.zero_inclusive_transform
  GeneratorSpec.negative_transform.

(** ** Types Module Extraction *)

(* Extract core types - use fully qualified names *)
Extraction "SolverTypesCore.ml"
  (* Core types *)
  SolverTypes.Digit
  SolverTypes.GridList
  SolverTypes.PossibilityCube

  (* Cage operation types *)
  SolverTypes.CageOp
  SolverTypes.Clue
  SolverTypes.clue_op
  SolverTypes.clue_value

  (* Cell types - Cell is a pair (nat * nat) *)
  SolverTypes.Cell
  SolverTypes.cell_to_index
  SolverTypes.index_to_cell
  SolverTypes.cell_in_bounds

  (* Cage structure *)
  SolverTypes.Cage
  SolverTypes.cage_cells
  SolverTypes.cage_clue

  (* Difficulty *)
  SolverTypes.Difficulty
  SolverTypes.diff_to_nat
  SolverTypes.diff_leb

  (* Mode flags *)
  SolverTypes.ModeFlags
  SolverTypes.has_mode
  SolverTypes.MODE_STANDARD
  SolverTypes.MODE_MULTIPLICATION
  SolverTypes.MODE_MYSTERY
  SolverTypes.MODE_ZERO_INCLUSIVE
  SolverTypes.MODE_NEGATIVE
  SolverTypes.MODE_EXPONENT
  SolverTypes.MODE_MODULAR
  SolverTypes.MODE_KILLER
  SolverTypes.MODE_BITWISE.

(** End of ExtractSolver *)
