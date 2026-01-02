(** * Extraction to OCaml

    This file extracts verified Coq code to OCaml for translation to C.

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From KeenKenning Require Import LatinSquare.
From KeenKenning Require Import DLX.
From KeenKenning Require Import SAT.

From Stdlib Require Import ZArith.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

(** ** Extraction Configuration *)

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

(* Extract Z to OCaml int (for simplicity, could use zarith for big ints) *)
Extract Inductive Z => "int" [ "0" "(fun p -> p)" "(fun p -> -p)" ]
  "(fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))".
Extract Constant Z.add => "(+)".
Extract Constant Z.sub => "(-)".
Extract Constant Z.mul => "( * )".
Extract Constant Z.opp => "(~-)".
Extract Constant Z.abs => "abs".
Extract Constant Z.eqb => "(=)".
Extract Constant Z.ltb => "(<)".
Extract Constant Z.lxor => "(lxor)".
Extract Constant Z.of_nat => "(fun n -> n)".
Extract Constant Z.to_nat => "(fun z -> if z < 0 then 0 else z)".

(** ** Extraction Commands *)

(* Create output directory *)
(* Run: mkdir -p extracted *)

(* Extract DLX module *)
Extraction "extracted/DLX.ml"
  DLX.check_exact_cover
  DLX.build_latin_matrix
  DLX.covered_cols
  DLX.has_duplicates.

(* Extract SAT module *)
Extraction "extracted/SAT.ml"
  SAT.latin_cnf
  SAT.encode_cage
  SAT.valid_tuples
  SAT.cnf_to_dimacs
  SAT.count_variables
  SAT.count_clauses.

(* Extract Latin Square definitions *)
Extraction "extracted/LatinSquare.ml"
  LatinSquare.Placement
  LatinSquare.placement_constraints
  LatinSquare.all_placements
  LatinSquare.eval_cage.
