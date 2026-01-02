(** * DSF: Disjoint Set Forest Specification

    Formal specification of the Disjoint Set Forest (Union-Find)
    data structure used for cage membership tracking in KenKen.

    The C implementation uses a packed encoding:
    - Bit 0: inverse flag (for extended DSF)
    - Bit 1: is_root flag
    - Bits 2-31: parent index (if not root) or size (if root)

    Reference: dsf.c from Simon Tatham's Portable Puzzle Collection

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Packed Encoding *)

(** Each element in the DSF array is packed as follows:
    - Bit 0: inverse flag (1 if this element is "opposite" to its parent)
    - Bit 1: root flag (1 if this is the root of its tree)
    - Bits 2+: if root, the size of the tree; otherwise, parent index

    Initial value is 6 = 0b110 = root flag set, size 1, no inverse *)

Definition DSF := list nat.

(** Unpack components from a DSF entry *)
Definition dsf_is_inverse (entry : nat) : bool :=
  Nat.testbit entry 0.

Definition dsf_is_root (entry : nat) : bool :=
  Nat.testbit entry 1.

Definition dsf_parent_or_size (entry : nat) : nat :=
  Nat.shiftr entry 2.

(** Pack components into a DSF entry *)
Definition dsf_pack_root (size : nat) : nat :=
  Nat.lor (Nat.shiftl size 2) 2.  (* size << 2 | 0b10 *)

Definition dsf_pack_child (parent : nat) (inverse : bool) : nat :=
  Nat.lor (Nat.shiftl parent 2) (if inverse then 1 else 0).

(** Initial DSF entry: root with size 1 *)
Definition dsf_init_entry : nat := 6.  (* 1 << 2 | 2 = 0b110 *)

(** ** DSF Operations *)

(** Initialize DSF of given size *)
Definition dsf_init (size : nat) : DSF :=
  repeat dsf_init_entry size.

(** Get entry at index *)
Definition dsf_get (dsf : DSF) (idx : nat) : option nat :=
  nth_error dsf idx.

(** Set entry at index *)
Fixpoint list_set {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  match l, idx with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S n => h :: list_set t n v
  end.

Definition dsf_set (dsf : DSF) (idx : nat) (entry : nat) : DSF :=
  list_set dsf idx entry.

(** ** Canonify (Find) Operation *)

(** Find the canonical (root) element of the equivalence class.
    Also returns the inverse flag accumulated along the path.

    This is a fuel-based version to ensure termination.
    The C version uses path compression which we model here. *)

(** Single step toward root *)
Definition canonify_step (dsf : DSF) (idx : nat) (inv : bool)
  : option (nat * bool * bool) :=  (* (next_idx, new_inv, is_root) *)
  match dsf_get dsf idx with
  | None => None
  | Some entry =>
      if dsf_is_root entry then
        Some (idx, inv, true)
      else
        let parent := dsf_parent_or_size entry in
        let step_inv := dsf_is_inverse entry in
        Some (parent, xorb inv step_inv, false)
  end.

(** Find root with fuel (for termination) *)
Fixpoint canonify_fuel (fuel : nat) (dsf : DSF) (idx : nat) (inv : bool)
  : option (nat * bool) :=
  match fuel with
  | 0 => None  (* Ran out of fuel - shouldn't happen in valid DSF *)
  | S fuel' =>
      match canonify_step dsf idx inv with
      | None => None
      | Some (next_idx, new_inv, is_root) =>
          if is_root then Some (next_idx, new_inv)
          else canonify_fuel fuel' dsf next_idx new_inv
      end
  end.

(** Canonify: find root of equivalence class containing idx.
    Returns (root_idx, inverse_flag).
    Uses DSF size as fuel (sufficient for any valid DSF). *)
Definition edsf_canonify (dsf : DSF) (idx : nat) : option (nat * bool) :=
  canonify_fuel (length dsf) dsf idx false.

(** Simple canonify without inverse tracking *)
Definition dsf_canonify (dsf : DSF) (idx : nat) : option nat :=
  match edsf_canonify dsf idx with
  | Some (root, _) => Some root
  | None => None
  end.

(** ** Size Operation *)

(** Get size of equivalence class containing idx *)
Definition dsf_size (dsf : DSF) (idx : nat) : option nat :=
  match dsf_canonify dsf idx with
  | None => None
  | Some root =>
      match dsf_get dsf root with
      | None => None
      | Some entry => Some (dsf_parent_or_size entry)
      end
  end.

(** ** Merge (Union) Operation *)

(** Merge two equivalence classes.
    The smaller index becomes the canonical element (deterministic for
    reproducible puzzle generation - see dsf.c comment lines 185-195).

    inverse = true means the two elements should be marked as "opposite" *)
Definition edsf_merge (dsf : DSF) (v1 v2 : nat) (inverse : bool) : option DSF :=
  match edsf_canonify dsf v1, edsf_canonify dsf v2 with
  | Some (r1, i1), Some (r2, i2) =>
      if Nat.eqb r1 r2 then
        (* Already in same class *)
        if Bool.eqb (xorb (xorb i1 i2) inverse) false then
          Some dsf  (* Consistent *)
        else
          None      (* Inconsistent inverse requirement *)
      else
        (* Different classes - merge them *)
        let final_inverse := xorb (xorb i1 i2) inverse in
        (* Make smaller index the new root *)
        let '(new_root, old_root) :=
          if Nat.ltb r1 r2 then (r1, r2) else (r2, r1) in
        match dsf_get dsf new_root, dsf_get dsf old_root with
        | Some entry1, Some entry2 =>
            let size1 := dsf_parent_or_size entry1 in
            let size2 := dsf_parent_or_size entry2 in
            (* Update new root's size *)
            let dsf' := dsf_set dsf new_root (dsf_pack_root (size1 + size2)) in
            (* Point old root to new root *)
            let dsf'' := dsf_set dsf' old_root (dsf_pack_child new_root final_inverse) in
            Some dsf''
        | _, _ => None
        end
  | _, _ => None
  end.

(** Simple merge without inverse *)
Definition dsf_merge (dsf : DSF) (v1 v2 : nat) : option DSF :=
  edsf_merge dsf v1 v2 false.

(** ** Path Compression *)

(** Apply path compression after canonify.
    Updates all elements on the path to point directly to root. *)
Fixpoint compress_path_fuel (fuel : nat) (dsf : DSF) (idx : nat)
  (root : nat) (final_inv : bool) (current_inv : bool) : DSF :=
  match fuel with
  | 0 => dsf
  | S fuel' =>
      if Nat.eqb idx root then dsf
      else
        match dsf_get dsf idx with
        | None => dsf
        | Some entry =>
            if dsf_is_root entry then dsf
            else
              let parent := dsf_parent_or_size entry in
              let step_inv := dsf_is_inverse entry in
              (* Update this node to point directly to root *)
              let rel_inv := xorb current_inv final_inv in
              let dsf' := dsf_set dsf idx (dsf_pack_child root rel_inv) in
              (* Continue to parent *)
              compress_path_fuel fuel' dsf' parent root final_inv
                (xorb current_inv step_inv)
        end
  end.

Definition compress_path (dsf : DSF) (idx : nat) (root : nat) (inv : bool) : DSF :=
  compress_path_fuel (length dsf) dsf idx root inv false.

(** Canonify with path compression *)
Definition dsf_canonify_compress (dsf : DSF) (idx : nat) : option (DSF * nat) :=
  match edsf_canonify dsf idx with
  | Some (root, inv) =>
      let dsf' := compress_path dsf idx root inv in
      Some (dsf', root)
  | None => None
  end.

(** ** Predicates *)

(** Two indices are in the same equivalence class *)
Definition dsf_equiv (dsf : DSF) (i j : nat) : Prop :=
  exists root,
    dsf_canonify dsf i = Some root /\
    dsf_canonify dsf j = Some root.

(** DSF is well-formed: all indices reachable, no cycles *)
Definition dsf_wf (dsf : DSF) : Prop :=
  forall idx, idx < length dsf ->
    exists root, dsf_canonify dsf idx = Some root /\ root < length dsf.

(** ** Key Theorems *)

(** Helper: canonify on initial DSF returns idx *)
Lemma canonify_init_returns_idx : forall n idx,
  idx < n ->
  dsf_canonify (dsf_init n) idx = Some idx.
Proof.
  intros n idx Hidx.
  unfold dsf_canonify, edsf_canonify, dsf_init.
  rewrite repeat_length.
  destruct n as [|n'].
  - lia.
  - cbn [canonify_fuel].
    unfold canonify_step, dsf_get.
    assert (Hnth: nth_error (repeat dsf_init_entry (S n')) idx = Some dsf_init_entry)
      by (apply nth_error_repeat; exact Hidx).
    rewrite Hnth.
    (* dsf_is_root dsf_init_entry = Nat.testbit 6 1 = true *)
    cbn [dsf_is_root dsf_init_entry].
    reflexivity.
Qed.

(** Length of initialized DSF *)
Lemma dsf_init_length : forall n, length (dsf_init n) = n.
Proof.
  intros n. unfold dsf_init. apply repeat_length.
Qed.

(** Initial DSF is well-formed *)
Theorem dsf_init_wf : forall n,
  dsf_wf (dsf_init n).
Proof.
  intros n. unfold dsf_wf.
  intros idx Hidx.
  rewrite dsf_init_length in *.
  exists idx.
  split.
  - apply canonify_init_returns_idx. exact Hidx.
  - exact Hidx.
Qed.

(** Helper: canonify_fuel only returns roots *)
Lemma canonify_fuel_returns_root :
  forall fuel dsf idx inv root final_inv,
    canonify_fuel fuel dsf idx inv = Some (root, final_inv) ->
    exists entry, dsf_get dsf root = Some entry /\ dsf_is_root entry = true.
Proof.
  induction fuel as [|fuel' IH]; intros dsf idx inv root final_inv Hcan.
  - (* fuel = 0 *)
    simpl in Hcan. discriminate.
  - (* fuel = S fuel' *)
    simpl in Hcan.
    unfold canonify_step in Hcan.
    destruct (dsf_get dsf idx) as [entry|] eqn:Eget; [|discriminate].
    destruct (dsf_is_root entry) eqn:Eroot.
    + (* idx is a root *)
      injection Hcan as Hroot Hinv.
      exists entry. split; [rewrite <- Hroot; exact Eget | exact Eroot].
    + (* idx is not a root - recurse *)
      eapply IH.
      exact Hcan.
Qed.

(** Canonify returns a root *)
Theorem canonify_is_root : forall dsf idx root,
  dsf_wf dsf ->
  dsf_canonify dsf idx = Some root ->
  match dsf_get dsf root with
  | Some entry => dsf_is_root entry = true
  | None => False
  end.
Proof.
  intros dsf idx root Hwf Hcan.
  unfold dsf_canonify in Hcan.
  destruct (edsf_canonify dsf idx) as [[r inv]|] eqn:Eedsf; [|discriminate].
  injection Hcan as Hroot. subst root.
  unfold edsf_canonify in Eedsf.
  apply canonify_fuel_returns_root in Eedsf.
  destruct Eedsf as [entry [Hget Hroot_flag]].
  rewrite Hget. exact Hroot_flag.
Qed.

(** Merge preserves well-formedness *)
Theorem dsf_merge_wf : forall dsf v1 v2 dsf',
  dsf_wf dsf ->
  v1 < length dsf ->
  v2 < length dsf ->
  dsf_merge dsf v1 v2 = Some dsf' ->
  dsf_wf dsf'.
Proof.
  intros dsf v1 v2 dsf' Hwf Hv1 Hv2 Hmerge.
  (* Merge maintains the invariants *)
  admit.
Admitted.

(** Merge creates equivalence *)
Theorem dsf_merge_equiv : forall dsf v1 v2 dsf',
  dsf_wf dsf ->
  dsf_merge dsf v1 v2 = Some dsf' ->
  dsf_equiv dsf' v1 v2.
Proof.
  intros dsf v1 v2 dsf' Hwf Hmerge.
  (* After merge, v1 and v2 have the same root *)
  admit.
Admitted.

(** Equivalence is reflexive *)
Theorem dsf_equiv_refl : forall dsf idx,
  dsf_wf dsf ->
  idx < length dsf ->
  dsf_equiv dsf idx idx.
Proof.
  intros dsf idx Hwf Hidx.
  unfold dsf_equiv.
  destruct (Hwf idx Hidx) as [root [Hcan _]].
  exists root. split; exact Hcan.
Qed.

(** Equivalence is symmetric *)
Theorem dsf_equiv_sym : forall dsf i j,
  dsf_equiv dsf i j -> dsf_equiv dsf j i.
Proof.
  intros dsf i j [root [Hi Hj]].
  exists root. split; [exact Hj | exact Hi].
Qed.

(** Equivalence is transitive *)
Theorem dsf_equiv_trans : forall dsf i j k,
  dsf_equiv dsf i j -> dsf_equiv dsf j k -> dsf_equiv dsf i k.
Proof.
  intros dsf i j k [r1 [Hi Hj]] [r2 [Hj' Hk]].
  assert (r1 = r2) by congruence.
  subst.
  exists r2. split; [exact Hi | exact Hk].
Qed.

(** Size after merge is sum of sizes *)
Theorem dsf_merge_size : forall dsf v1 v2 dsf' s1 s2,
  dsf_wf dsf ->
  dsf_size dsf v1 = Some s1 ->
  dsf_size dsf v2 = Some s2 ->
  ~ dsf_equiv dsf v1 v2 ->
  dsf_merge dsf v1 v2 = Some dsf' ->
  dsf_size dsf' v1 = Some (s1 + s2).
Proof.
  intros dsf v1 v2 dsf' s1 s2 Hwf Hs1 Hs2 Hneq Hmerge.
  (* New size is sum of old sizes *)
  admit.
Admitted.

(** ** Extraction *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

(** End of DSF specification *)
