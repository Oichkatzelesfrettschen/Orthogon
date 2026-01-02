(** * Verified Extraction to OCaml/Malfunction

    This file uses rocq-verified-extraction for certified code extraction.
    The extraction process itself is proven correct (PLDI 2024).

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From KeenKenning Require Import SolverTypes.
From KeenKenning Require Import DSF.
From KeenKenning Require Import CageOps.

(** Import verified extraction infrastructure *)
From VerifiedExtraction Require Import Extraction.

(** ** DSF Operations Extraction *)

(** Initialize DSF of given size *)
Verified Extraction dsf_init.

(** Find root of equivalence class *)
Verified Extraction dsf_canonify.

(** Merge two equivalence classes *)
Verified Extraction dsf_merge.

(** Get size of equivalence class *)
Verified Extraction dsf_size.

(** Path compression *)
Verified Extraction dsf_canonify_compress.

(** ** Cage Operations Extraction *)

(** Evaluate cage operation on values *)
Verified Extraction eval_cage_op.

(** Check cage satisfaction (boolean) *)
Verified Extraction cage_satisfiedb.

(** ** Latin Square Core *)

(** Validate cell is in bounds *)
Verified Extraction cell_to_index.

(** Get digit at position *)
Verified Extraction grid_get.

(** ** File Extraction *)

(** Extract to Malfunction files for native compilation *)
Verified Extraction dsf_init "extracted/dsf_init.mlf".
Verified Extraction dsf_canonify "extracted/dsf_canonify.mlf".
Verified Extraction cage_satisfiedb "extracted/cage_satisfiedb.mlf".

(** Note: Compile Malfunction files with:
    malfunction compile extracted/dsf_init.mlf -o extracted/dsf_init.o
    Then link with C FFI bridge. *)

(** ** Verification Notes *)

(** The key theorem from rocq-verified-extraction:
    For any term t that evaluates to value v in Rocq,
    the erased term erased(t) evaluates to erased(v).

    This is proven in the VerifiedExtraction library. *)

Print Assumptions dsf_canonify.
Print Assumptions cage_satisfiedb.

(** End of Verified Extraction *)
