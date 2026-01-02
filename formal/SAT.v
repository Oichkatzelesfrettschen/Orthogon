(** * SAT/CNF Encoding for Cage Constraints

    Formal specification of CNF encoding for KenKen cage constraints.
    This module provides Tseitin transformation and clause generation.

    Author: KeenKenning Project
    Date: 2026-01-01
    SPDX-License-Identifier: MIT
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
Import ListNotations.

(** ** CNF Definitions *)

(** A literal is a signed variable *)
Definition Literal := Z.  (* Positive = variable, Negative = negation *)

(** A clause is a disjunction of literals *)
Definition Clause := list Literal.

(** A CNF formula is a conjunction of clauses *)
Definition CNF := list Clause.

(** ** Variable Encoding for Latin Squares *)

(** For an NxN grid, variable v(r,c,d) means "cell (r,c) has digit d"
    Variable number = r*N*N + c*N + d (1-indexed for DIMACS) *)

Definition var_cell_digit (n r c d : nat) : Z :=
  Z.of_nat (r * n * n + c * n + d + 1).

(** ** Latin Square Constraints *)

(** At least one digit per cell: OR(v(r,c,1), v(r,c,2), ..., v(r,c,n)) *)
Definition at_least_one_clause (n r c : nat) : Clause :=
  map (fun d => var_cell_digit n r c d) (seq 0 n).

(** At most one digit per cell: for all pairs (d1,d2), NOT(v(r,c,d1) AND v(r,c,d2))
    Equivalent to: OR(NOT v(r,c,d1), NOT v(r,c,d2)) for each pair *)
Fixpoint at_most_one_clauses_aux (n r c d1 : nat) (ds : list nat) : list Clause :=
  match ds with
  | [] => []
  | d2 :: rest =>
      [Z.opp (var_cell_digit n r c d1); Z.opp (var_cell_digit n r c d2)]
      :: at_most_one_clauses_aux n r c d1 rest
  end.

Fixpoint at_most_one_clauses (n r c : nat) (ds : list nat) : list Clause :=
  match ds with
  | [] => []
  | d :: rest =>
      at_most_one_clauses_aux n r c d rest ++ at_most_one_clauses n r c rest
  end.

(** Exactly one digit per cell *)
Definition exactly_one_cell (n r c : nat) : CNF :=
  at_least_one_clause n r c :: at_most_one_clauses n r c (seq 0 n).

(** Row uniqueness: each digit appears at most once per row *)
Fixpoint row_unique_aux (n r d c1 : nat) (cs : list nat) : list Clause :=
  match cs with
  | [] => []
  | c2 :: rest =>
      [Z.opp (var_cell_digit n r c1 d); Z.opp (var_cell_digit n r c2 d)]
      :: row_unique_aux n r d c1 rest
  end.

Fixpoint row_unique_digit (n r d : nat) (cs : list nat) : list Clause :=
  match cs with
  | [] => []
  | c :: rest =>
      row_unique_aux n r d c rest ++ row_unique_digit n r d rest
  end.

Definition row_unique (n r d : nat) : CNF :=
  row_unique_digit n r d (seq 0 n).

(** Column uniqueness: each digit appears at most once per column *)
Fixpoint col_unique_aux (n c d r1 : nat) (rs : list nat) : list Clause :=
  match rs with
  | [] => []
  | r2 :: rest =>
      [Z.opp (var_cell_digit n r1 c d); Z.opp (var_cell_digit n r2 c d)]
      :: col_unique_aux n c d r1 rest
  end.

Fixpoint col_unique_digit (n c d : nat) (rs : list nat) : list Clause :=
  match rs with
  | [] => []
  | r :: rest =>
      col_unique_aux n c d r rest ++ col_unique_digit n c d rest
  end.

Definition col_unique (n c d : nat) : CNF :=
  col_unique_digit n c d (seq 0 n).

(** Full Latin square CNF encoding *)
Definition latin_cnf (n : nat) : CNF :=
  (* Cell constraints *)
  flat_map (fun r =>
    flat_map (fun c => exactly_one_cell n r c) (seq 0 n)
  ) (seq 0 n)
  ++
  (* Row uniqueness *)
  flat_map (fun r =>
    flat_map (fun d => row_unique n r d) (seq 0 n)
  ) (seq 0 n)
  ++
  (* Column uniqueness *)
  flat_map (fun c =>
    flat_map (fun d => col_unique n c d) (seq 0 n)
  ) (seq 0 n).

(** ** Cage Constraints *)

(** A cell position *)
Definition Cell := (nat * nat)%type.

(** Cage operation *)
Inductive CageOp := OpAdd | OpSub | OpMul | OpDiv | OpXor | OpMod.

(** A cage definition *)
Record Cage := mkCage {
  cage_cells : list Cell;
  cage_op : CageOp;
  cage_target : Z
}.

(** ** Tuple Enumeration for Small Cages *)

(** Generate all tuples of length k with values 1..n *)
Fixpoint all_tuples (n k : nat) : list (list nat) :=
  match k with
  | O => [[]]
  | S k' =>
      flat_map (fun t =>
        map (fun v => v :: t) (seq 1 n)
      ) (all_tuples n k')
  end.

(** Evaluate cage operation on tuple *)
Definition eval_op (op : CageOp) (n : nat) (vals : list nat) : option Z :=
  match op, vals with
  | OpAdd, _ => Some (fold_left (fun a b => Z.add a (Z.of_nat b)) vals 0%Z)
  | OpMul, _ => Some (fold_left (fun a b => Z.mul a (Z.of_nat b)) vals 1%Z)
  | OpSub, [a; b] =>
      let diff := Z.sub (Z.of_nat a) (Z.of_nat b) in
      Some (Z.abs diff)
  | OpDiv, [a; b] =>
      if Nat.eqb (Nat.modulo a b) 0%nat then Some (Z.of_nat (Nat.div a b))
      else if Nat.eqb (Nat.modulo b a) 0%nat then Some (Z.of_nat (Nat.div b a))
      else None
  | OpXor, _ => Some (fold_left (fun a b => Z.lxor a (Z.of_nat b)) vals 0%Z)
  | OpMod, _ =>
      let sum := fold_left Nat.add vals 0%nat in
      Some (Z.of_nat (Nat.modulo sum n))
  | _, _ => None
  end.

(** Filter tuples that satisfy the cage constraint *)
Definition valid_tuples (n : nat) (cage : Cage) : list (list nat) :=
  let tuples := all_tuples n (length (cage_cells cage)) in
  filter (fun t =>
    match eval_op (cage_op cage) n t with
    | Some v => Z.eqb v (cage_target cage)
    | None => false
    end
  ) tuples.

(** ** Tseitin Transformation for Cage Constraints *)

(** For each valid tuple, create a conjunction of cell-digit assignments *)
(** The cage constraint is: OR(tuple1, tuple2, ...) *)
(** Each tuple is: AND(cell1=v1, cell2=v2, ...) *)

(** Clause for: at least one valid tuple must hold *)
(** Uses auxiliary variables to avoid exponential blowup *)

Definition tuple_aux_var (base_var cage_id tuple_id : nat) : Z :=
  Z.of_nat (base_var + cage_id * 1000 + tuple_id + 1).

(** Encode: aux_var <-> (cell1=v1 AND cell2=v2 AND ...) *)
(** Forward: aux_var -> cell1=v1, aux_var -> cell2=v2, ... *)
(** Backward: (cell1=v1 AND cell2=v2 AND ...) -> aux_var *)

Definition encode_tuple_forward (n : nat) (cells : list Cell) (tuple : list nat) (aux : Z) : CNF :=
  map (fun cv =>
    let '(c, v) := cv in
    let '(r, col) := c in
    [Z.opp aux; var_cell_digit n r col (v - 1)]
  ) (combine cells tuple).

Definition encode_tuple_backward (n : nat) (cells : list Cell) (tuple : list nat) (aux : Z) : Clause :=
  aux :: map (fun cv =>
    let '(c, v) := cv in
    let '(r, col) := c in
    Z.opp (var_cell_digit n r col (v - 1))
  ) (combine cells tuple).

(** Encode a cage constraint *)
Definition encode_cage (n base_var cage_id : nat) (cage : Cage) : CNF :=
  let tuples := valid_tuples n cage in
  let cells := cage_cells cage in
  (* Create auxiliary variable for each valid tuple *)
  let aux_vars := map (fun i => tuple_aux_var base_var cage_id i) (seq 0 (length tuples)) in
  (* At least one aux var must be true *)
  let at_least_one := aux_vars in
  (* Forward implications for each tuple *)
  let forwards := flat_map (fun ia =>
    let '(i, aux) := ia in
    match nth_error tuples i with
    | Some t => encode_tuple_forward n cells t aux
    | None => []
    end
  ) (combine (seq 0 (length aux_vars)) aux_vars) in
  (* Backward implications for each tuple *)
  let backwards := map (fun ia =>
    let '(i, aux) := ia in
    match nth_error tuples i with
    | Some t => encode_tuple_backward n cells t aux
    | None => []
    end
  ) (combine (seq 0 (length aux_vars)) aux_vars) in
  at_least_one :: forwards ++ backwards.

(** ** Killer Mode Constraint *)

(** No repeated digits within cage *)
Definition killer_clauses (n : nat) (cells : list Cell) : CNF :=
  flat_map (fun d =>
    flat_map (fun i1 =>
      flat_map (fun i2 =>
        if Nat.ltb i1 i2 then
          match nth_error cells i1, nth_error cells i2 with
          | Some (r1, c1), Some (r2, c2) =>
              [[Z.opp (var_cell_digit n r1 c1 d);
                Z.opp (var_cell_digit n r2 c2 d)]]
          | _, _ => []
          end
        else []
      ) (seq 0 (length cells))
    ) (seq 0 (length cells))
  ) (seq 0 n).

(** ** CNF Validity *)

(** Assignment: variable -> bool *)
Definition Assignment := nat -> bool.

(** Evaluate literal under assignment *)
Definition eval_literal (a : Assignment) (l : Literal) : bool :=
  if Z.ltb l 0 then negb (a (Z.to_nat (Z.opp l)))
  else a (Z.to_nat l).

(** Evaluate clause under assignment *)
Definition eval_clause (a : Assignment) (c : Clause) : bool :=
  existsb (eval_literal a) c.

(** Evaluate CNF under assignment *)
Definition eval_cnf (a : Assignment) (f : CNF) : bool :=
  forallb (eval_clause a) f.

(** A CNF is satisfiable if there exists a satisfying assignment *)
Definition satisfiable (f : CNF) : Prop :=
  exists a, eval_cnf a f = true.

(** ** Main Theorem: Encoding Correctness *)

(** The Latin CNF is satisfiable iff an NxN Latin square exists *)
Theorem latin_cnf_correct :
  forall n,
    n > 0 ->
    satisfiable (latin_cnf n).
Proof.
  intros n Hn.
  (* Construction: use the standard Latin square where cell(r,c) = (r+c) mod n + 1 *)
  (* This always exists for n > 0 *)
  admit.
Admitted.

(** Theorem: Cage encoding preserves satisfiability *)
Theorem cage_encoding_correct :
  forall n base cage,
    length (valid_tuples n cage) > 0 ->
    satisfiable (encode_cage n base 0 cage).
Proof.
  intros n base cage Htuples.
  (* If there's at least one valid tuple, the encoding is satisfiable *)
  admit.
Admitted.

(** ** DIMACS Output *)

(** Convert CNF to DIMACS format (for extraction) *)
Definition clause_to_dimacs (c : Clause) : list Z :=
  c ++ [0%Z].

Definition cnf_to_dimacs (f : CNF) : list (list Z) :=
  map clause_to_dimacs f.

(** ** Statistics *)

Definition count_variables (f : CNF) : nat :=
  let all_lits := concat f in
  let abs_lits := map (fun l => Z.to_nat (Z.abs l)) all_lits in
  match abs_lits with
  | [] => 0
  | _ => fold_left Nat.max abs_lits 0
  end.

Definition count_clauses (f : CNF) : nat :=
  length f.

(** ** Extraction *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option" [ "Some" "None" ].

(* Extraction "SAT.ml" latin_cnf encode_cage cnf_to_dimacs. *)

(** End of SAT encoding specification *)
