(** * CageOps: Cage Operation Semantics

    Formal semantics for all 11 cage operations in KenKen puzzles.
    These operations define how digits in a cage combine to produce
    the clue value.

    Operations are categorized by:
    - Arity: binary-only (Sub, Div, Exp, Mod) vs n-ary (Add, Mul, Xor, And, Or, Gcd, Lcm)
    - Algebraic properties: commutative, associative, identity element
    - Constraint complexity: affects solver difficulty

    Reference: keen_solver.c solver_common switch statement

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Nat.
Import ListNotations.

From KeenKenning Require Import SolverTypes.

(** ** Binary Helpers *)

(** GCD and LCM from standard library (Rocq 9.0+).
    Nat.gcd implements Euclidean algorithm.
    Nat.lcm computes a * (b / gcd(a,b)). *)
Definition gcd := Nat.gcd.
Definition lcm := Nat.lcm.

(** Power function: base^exp *)
Fixpoint pow (base exp : nat) : nat :=
  match exp with
  | 0 => 1
  | S e' => base * pow base e'
  end.

(** Fold operations for n-ary functions *)
Definition fold_add (digits : list nat) : nat :=
  fold_left Nat.add digits 0.

Definition fold_mul (digits : list nat) : nat :=
  fold_left Nat.mul digits 1.

Definition fold_xor (digits : list nat) : nat :=
  fold_left Nat.lxor digits 0.

Definition fold_and (digits : list nat) : nat :=
  match digits with
  | [] => 0
  | d :: ds => fold_left Nat.land ds d
  end.

Definition fold_or (digits : list nat) : nat :=
  fold_left Nat.lor digits 0.

Definition fold_gcd (digits : list nat) : nat :=
  match digits with
  | [] => 0
  | d :: ds => fold_left gcd ds d
  end.

Definition fold_lcm (digits : list nat) : nat :=
  match digits with
  | [] => 1
  | d :: ds => fold_left lcm ds d
  end.

(** ** Operation Evaluation *)

(** Evaluate a cage operation on a list of digits.
    Returns None if operation is undefined for the given inputs
    (e.g., division by zero, wrong arity for binary ops). *)

Definition eval_add (digits : list nat) : option nat :=
  Some (fold_add digits).

Definition eval_mul (digits : list nat) : option nat :=
  Some (fold_mul digits).

(** Subtraction: larger - smaller for exactly 2 digits *)
Definition eval_sub (digits : list nat) : option nat :=
  match digits with
  | [a; b] => Some (Nat.max a b - Nat.min a b)
  | _ => None
  end.

(** Division: larger / smaller for exactly 2 digits, must divide evenly *)
Definition eval_div (digits : list nat) : option nat :=
  match digits with
  | [a; b] =>
      let larger := Nat.max a b in
      let smaller := Nat.min a b in
      match smaller with
      | 0 => None  (* Division by zero *)
      | _ =>
          if Nat.eqb (larger mod smaller) 0
          then Some (larger / smaller)
          else None  (* Must divide evenly *)
      end
  | _ => None
  end.

(** Exponent: smaller^larger = result for exactly 2 digits *)
Definition eval_exp (digits : list nat) : option nat :=
  match digits with
  | [a; b] =>
      let base := Nat.min a b in
      let exponent := Nat.max a b in
      Some (pow base exponent)
  | _ => None
  end.

(** Modulo: larger mod smaller for exactly 2 digits *)
Definition eval_mod (digits : list nat) : option nat :=
  match digits with
  | [a; b] =>
      let larger := Nat.max a b in
      let smaller := Nat.min a b in
      match smaller with
      | 0 => None  (* Mod by zero *)
      | _ => Some (larger mod smaller)
      end
  | _ => None
  end.

Definition eval_xor (digits : list nat) : option nat :=
  Some (fold_xor digits).

Definition eval_and (digits : list nat) : option nat :=
  Some (fold_and digits).

Definition eval_or (digits : list nat) : option nat :=
  Some (fold_or digits).

Definition eval_gcd (digits : list nat) : option nat :=
  Some (fold_gcd digits).

Definition eval_lcm (digits : list nat) : option nat :=
  Some (fold_lcm digits).

(** Master evaluation function *)
Definition eval_cage_op (op : CageOp) (digits : list nat) : option nat :=
  match op with
  | OpAdd => eval_add digits
  | OpMul => eval_mul digits
  | OpSub => eval_sub digits
  | OpDiv => eval_div digits
  | OpXor => eval_xor digits
  | OpAnd => eval_and digits
  | OpOr  => eval_or digits
  | OpExp => eval_exp digits
  | OpMod => eval_mod digits
  | OpGcd => eval_gcd digits
  | OpLcm => eval_lcm digits
  end.

(** ** Cage Satisfaction *)

(** A cage is satisfied when digits evaluate to clue value *)
Definition cage_satisfied (cage : Cage) (digits : list nat) : Prop :=
  match eval_cage_op (clue_op (cage_clue cage)) digits with
  | Some v => Z.of_nat v = clue_value (cage_clue cage)
  | None => False
  end.

(** Boolean version for computation *)
Definition cage_satisfiedb (cage : Cage) (digits : list nat) : bool :=
  match eval_cage_op (clue_op (cage_clue cage)) digits with
  | Some v => Z.eqb (Z.of_nat v) (clue_value (cage_clue cage))
  | None => false
  end.

(** ** Operation Properties *)

(** Default value for option *)
Definition option_default {A : Type} (default : A) (o : option A) : A :=
  match o with
  | Some v => v
  | None => default
  end.

(** Operation is commutative: order of digits doesn't matter *)
Definition op_commutative (op : CageOp) : Prop :=
  forall digits, eval_cage_op op digits = eval_cage_op op (rev digits).

(** Operation is associative: grouping doesn't matter *)
Definition op_associative (op : CageOp) : Prop :=
  forall a b c,
    let bc := option_default 0 (eval_cage_op op [b; c]) in
    let ab := option_default 0 (eval_cage_op op [a; b]) in
    eval_cage_op op [a; bc] = eval_cage_op op [ab; c].

(** Operation has identity element *)
Definition has_identity (op : CageOp) (id : nat) : Prop :=
  forall d, eval_cage_op op [d] = Some d /\
            eval_cage_op op [d; id] = Some d.

(** Binary operation only (exactly 2 digits required) *)
Definition is_binary_only (op : CageOp) : Prop :=
  forall d, eval_cage_op op [d] = None /\
            forall ds, length ds > 2 -> eval_cage_op op ds = None.

(** ** Key Theorems *)

(** Evaluation is deterministic *)
Theorem eval_deterministic : forall op digits v1 v2,
  eval_cage_op op digits = Some v1 ->
  eval_cage_op op digits = Some v2 ->
  v1 = v2.
Proof.
  intros op digits v1 v2 H1 H2.
  rewrite H1 in H2.
  injection H2. auto.
Qed.

(** Addition is commutative *)
Theorem add_commutative : forall a b,
  eval_add [a; b] = eval_add [b; a].
Proof.
  intros a b.
  unfold eval_add, fold_add.
  simpl. f_equal. lia.
Qed.

(** Multiplication is commutative *)
Theorem mul_commutative : forall a b,
  eval_mul [a; b] = eval_mul [b; a].
Proof.
  intros a b.
  unfold eval_mul, fold_mul.
  simpl. f_equal. lia.
Qed.

(** XOR is self-inverse: a XOR a = 0 *)
Theorem xor_self_inverse : forall a,
  Nat.lxor a a = 0.
Proof.
  intros a.
  apply Nat.lxor_nilpotent.
Qed.

(** XOR identity: a XOR 0 = a *)
Theorem xor_identity : forall a,
  Nat.lxor a 0 = a.
Proof.
  intros a.
  apply Nat.lxor_0_r.
Qed.

(** XOR is commutative *)
Theorem xor_commutative : forall a b,
  eval_xor [a; b] = eval_xor [b; a].
Proof.
  intros a b.
  unfold eval_xor, fold_xor.
  simpl. f_equal.
  rewrite Nat.lxor_0_l.
  rewrite Nat.lxor_0_l.
  apply Nat.lxor_comm.
Qed.

(** XOR is associative *)
Theorem xor_associative : forall a b c,
  Nat.lxor (Nat.lxor a b) c = Nat.lxor a (Nat.lxor b c).
Proof.
  intros a b c.
  apply Nat.lxor_assoc.
Qed.

(** Subtraction is always non-negative (our definition) *)
Theorem sub_nonneg : forall a b v,
  eval_sub [a; b] = Some v ->
  v >= 0.
Proof.
  intros a b v H.
  unfold eval_sub in H.
  injection H as H. subst.
  lia.
Qed.

(** Division result * divisor = dividend (when it divides evenly) *)
Theorem div_inverse : forall a b v,
  eval_div [a; b] = Some v ->
  v * Nat.min a b = Nat.max a b.
Proof.
  intros a b v H.
  unfold eval_div in H.
  destruct (Nat.min a b) as [|n] eqn:Hmin.
  - discriminate H.
  - destruct (Nat.max a b mod S n =? 0) eqn:Hmod.
    + injection H as Hv. subst v.
      apply Nat.eqb_eq in Hmod.
      (* Goal: (Nat.max a b / S n) * S n = Nat.max a b *)
      (* Use Nat.div_mod: a = b * (a / b) + a mod b *)
      pose proof (Nat.div_mod (Nat.max a b) (S n) ltac:(discriminate)) as Hdm.
      (* Hdm: Nat.max a b = S n * (Nat.max a b / S n) + Nat.max a b mod S n *)
      rewrite Hmod, Nat.add_0_r in Hdm.
      (* Hdm: Nat.max a b = S n * (Nat.max a b / S n) *)
      rewrite Nat.mul_comm.
      (* Goal: S n * (Nat.max a b / S n) = Nat.max a b *)
      symmetry.
      exact Hdm.
    + discriminate H.
Qed.

(** GCD divides both inputs *)
Theorem gcd_divides_both : forall a b,
  Nat.divide (gcd a b) a /\ Nat.divide (gcd a b) b.
Proof.
  intros a b.
  unfold gcd.
  split; [apply Nat.gcd_divide_l | apply Nat.gcd_divide_r].
Qed.

(** LCM is multiple of both inputs *)
Theorem lcm_multiple_both : forall a b,
  a > 0 -> b > 0 ->
  Nat.divide a (lcm a b) /\ Nat.divide b (lcm a b).
Proof.
  intros a b _ _.
  unfold lcm.
  split; [apply Nat.divide_lcm_l | apply Nat.divide_lcm_r].
Qed.

(** Binary operations require exactly 2 inputs *)
Theorem sub_binary : forall d,
  eval_sub [d] = None.
Proof.
  intros d. reflexivity.
Qed.

Theorem div_binary : forall d,
  eval_div [d] = None.
Proof.
  intros d. reflexivity.
Qed.

Theorem exp_binary : forall d,
  eval_exp [d] = None.
Proof.
  intros d. reflexivity.
Qed.

Theorem mod_binary : forall d,
  eval_mod [d] = None.
Proof.
  intros d. reflexivity.
Qed.

(** ** Operation Ambiguity Analysis *)

(** XOR has higher ambiguity than standard ops.
    For a 2-cell cage with digits in [1,n], XOR can produce n different
    results (0 to n-1 via XOR), while Sub/Div are constrained. *)

(** Count valid digit pairs for a given clue *)
Definition count_pairs_sub (n target : nat) : nat :=
  length (filter (fun ab =>
    let a := fst ab in
    let b := snd ab in
    Nat.max a b - Nat.min a b =? target
  ) (list_prod (seq 1 n) (seq 1 n))).

Definition count_pairs_xor (n target : nat) : nat :=
  length (filter (fun ab =>
    let a := fst ab in
    let b := snd ab in
    Nat.lxor a b =? target
  ) (list_prod (seq 1 n) (seq 1 n))).

(** XOR ambiguity is higher for most targets *)
(* This is verified empirically in the solver *)

(** ** Operation Classification *)

(** Classify operations by their properties *)
Record OpClass := mkOpClass {
  oc_op : CageOp;
  oc_binary_only : bool;     (* Exactly 2 inputs required *)
  oc_commutative : bool;     (* Order doesn't matter *)
  oc_associative : bool;     (* Grouping doesn't matter *)
  oc_identity : option nat   (* Identity element if exists *)
}.

Definition classify_op (op : CageOp) : OpClass :=
  match op with
  | OpAdd => mkOpClass OpAdd false true true (Some 0)
  | OpMul => mkOpClass OpMul false true true (Some 1)
  | OpSub => mkOpClass OpSub true true false None
  | OpDiv => mkOpClass OpDiv true true false None
  | OpXor => mkOpClass OpXor false true true (Some 0)
  | OpAnd => mkOpClass OpAnd false true true None  (* No universal identity *)
  | OpOr  => mkOpClass OpOr  false true true (Some 0)
  | OpExp => mkOpClass OpExp true false false None  (* NOT commutative: 2^3 ≠ 3^2 *)
  | OpMod => mkOpClass OpMod true false false None  (* NOT commutative: 5%3 ≠ 3%5 *)
  | OpGcd => mkOpClass OpGcd false true true None   (* No universal identity *)
  | OpLcm => mkOpClass OpLcm false true true (Some 1)
  end.

(** ** Cage Validity *)

(** Valid cage: cells form contiguous region, clue is satisfiable *)
Definition cage_valid (n : nat) (cage : Cage) : Prop :=
  let cells := cage_cells cage in
  (* All cells in bounds *)
  (forall c, In c cells -> cell_in_bounds n c) /\
  (* Cage not empty *)
  length cells > 0 /\
  (* For binary ops, exactly 2 cells *)
  (match clue_op (cage_clue cage) with
   | OpSub | OpDiv | OpExp | OpMod => length cells = 2
   | _ => True
   end).

(** Cage has at least one valid solution *)
Definition cage_solvable (n : nat) (cage : Cage) : Prop :=
  exists digits,
    length digits = length (cage_cells cage) /\
    (forall d, In d digits -> 1 <= d /\ d <= n) /\
    cage_satisfied cage digits.

(** ** Reflection Theorems *)

(** Link between boolean cage_satisfiedb and propositional cage_satisfied *)
Theorem cage_satisfiedb_reflect :
  forall cage digits,
    cage_satisfiedb cage digits = true <-> cage_satisfied cage digits.
Proof.
  intros cage digits.
  unfold cage_satisfiedb, cage_satisfied.
  destruct (eval_cage_op (clue_op (cage_clue cage)) digits) as [v|] eqn:Eval.
  - (* Some v case *)
    split.
    + intros H. apply Z.eqb_eq in H. exact H.
    + intros H. apply Z.eqb_eq. exact H.
  - (* None case *)
    split.
    + intros H. discriminate.
    + intros H. destruct H.
Qed.

(** Decidability of cage satisfaction *)
Corollary cage_satisfied_dec :
  forall cage digits, {cage_satisfied cage digits} + {~ cage_satisfied cage digits}.
Proof.
  intros cage digits.
  destruct (cage_satisfiedb cage digits) eqn:E.
  - left. apply cage_satisfiedb_reflect. exact E.
  - right. intro H. apply cage_satisfiedb_reflect in H. rewrite H in E. discriminate.
Qed.

(** If boolean test passes, digits satisfy the cage *)
Corollary cage_satisfiedb_sound :
  forall cage digits,
    cage_satisfiedb cage digits = true ->
    cage_satisfied cage digits.
Proof.
  intros cage digits H.
  apply cage_satisfiedb_reflect. exact H.
Qed.

(** If boolean test fails, digits don't satisfy the cage *)
Corollary cage_satisfiedb_complete :
  forall cage digits,
    cage_satisfied cage digits ->
    cage_satisfiedb cage digits = true.
Proof.
  intros cage digits H.
  apply cage_satisfiedb_reflect. exact H.
Qed.

(** ** Extraction Hints *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

(** End of CageOps *)
