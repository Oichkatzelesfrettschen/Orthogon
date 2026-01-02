# Enumeration Proof Strategy
**Date**: 2026-01-02
**Goal**: Prove correctness of candidate enumeration and resolve all admitted lemmas

---

## 1. Algorithm Analysis

### Core Recursion Structure

```
enumerate_candidates_aux(o, cage, cube, cells, partial, i, fuel):
  if fuel = 0: return []
  if i < length(cells):
    match find_next_digit(o, cage, cube, cells, partial, i, 1, S o):
      Some d -> recurse with (partial ++ [d], i+1, fuel-1)
      None   -> return []  (backtrack)
  else:  // i >= length(cells)
    if cage_satisfiedb(cage, partial):
      return [partial]
    else:
      return []
```

### Key Invariants

1. **Partial Assignment Validity**: At each recursive call, `partial` satisfies:
   - Length = i
   - Each digit in bounds [1, o]
   - No Latin square violations (row/column uniqueness)
   - Each digit respects cube constraints

2. **Monotonic Progress**: Each recursive call either:
   - Extends partial assignment (i increases)
   - Returns empty list (backtrack)

3. **Termination**: Fuel decreases on each recursive call

---

## 2. Helper Lemma Dependencies

### Graph of Dependencies

```
digit_valid_correctness
    |
    v
find_next_digit_soundness ----+
    |                         |
    v                         v
find_next_digit_complete   enumerate_aux_sound
    |                         |
    +-------------------------+
                |
                v
         enumeration_sound


partial_assignment_valid
    |
    v
enumerate_aux_complete -----> enumeration_complete
    |
    v
backtracking_explores_all


iscratch_setbit_correct
    |
    v
fold_left_accumulation -----> iscratch_update_sound
```

---

## 3. Required Helper Lemmas

### 3.1 digit_valid_for_position Correctness

```coq
Lemma digit_valid_implies_constraints :
  forall o cage cube cells partial i d,
    i = length partial ->
    digit_valid_for_position o cage cube cells partial i d = true ->
    (* d in bounds *)
    1 <= d <= o /\
    (* d in cube *)
    (let (x, y) := nth i cells (0, 0) in cube_get o cube x y d = true) /\
    (* No Latin violations *)
    (forall j, j < i ->
      let d_j := nth j partial 0 in
      let (x_i, y_i) := nth i cells (0, 0) in
      let (x_j, y_j) := nth j cells (0, 0) in
      d_j <> 0 ->
      (x_i <> x_j \/ d = d_j) /\
      (y_i <> y_j \/ d = d_j)).
```

### 3.2 find_next_digit Soundness

```coq
Lemma find_next_digit_sound :
  forall fuel o cage cube cells partial i start_d d,
    find_next_digit o cage cube cells partial i start_d fuel = Some d ->
    digit_valid_for_position o cage cube cells partial i d = true /\
    start_d <= d <= o.
```

### 3.3 find_next_digit Completeness

```coq
Lemma find_next_digit_complete :
  forall o cage cube cells partial i d,
    1 <= d <= o ->
    digit_valid_for_position o cage cube cells partial i d = true ->
    exists fuel,
      find_next_digit o cage cube cells partial i 1 fuel = Some d' /\
      d' <= d.
```

### 3.4 Partial Assignment Preservation

```coq
Lemma partial_extends_preserves_validity :
  forall o cube cells partial i d,
    i = length partial ->
    digit_valid_for_position o cage cube cells partial i d = true ->
    (* Extended partial is still valid *)
    forall j, j < i ->
      let d_j := nth j partial 0 in
      let d_new := nth j (partial ++ [d]) 0 in
      d_j = d_new.
```

---

## 4. Main Theorem Proof Strategies

### 4.1 enumeration_sound

**Strategy**: Strong induction on fuel + case analysis

**Proof Outline**:
```coq
Proof by induction on fuel:
  Base: fuel = 0 -> empty list -> vacuously true

  Step: fuel = S fuel'
    Case i < length cells:
      Match find_next_digit:
        Some d:
          By find_next_digit_sound: d is valid
          By IH: recursive result is sound
          Therefore: all candidates satisfy cage
        None:
          Empty list -> vacuously true

    Case i >= length cells:
      Only return [partial] if cage_satisfiedb = true
      Therefore: all candidates satisfy cage
```

**Required Lemmas**: find_next_digit_sound

---

### 4.2 enumeration_complete

**Strategy**: Constructive - build enumeration trace for given solution

**Proof Outline**:
```coq
Given: solution satisfying cage and cube constraints

Construct enumeration sequence:
  Step 0: partial = [], i = 0
  Step 1: partial = [solution[0]], i = 1  (via find_next_digit)
  ...
  Step n: partial = solution, i = n

Prove by induction that each step is reachable:
  Base: Start with partial = []

  Step: Assume partial = solution[0..i-1] is reachable
    Show: find_next_digit returns solution[i]
      By hypothesis: solution[i] satisfies cube
      By hypothesis: no Latin violations
      Therefore: digit_valid_for_position = true
      By find_next_digit_complete: found

    Therefore: recurse with partial ++ [solution[i]]
    By IH: reach complete solution
```

**Required Lemmas**:
- find_next_digit_complete
- partial_extends_preserves_validity
- digit_valid_implies_constraints

---

### 4.3 iscratch_update_sound

**Strategy**: fold_left induction + setbit correctness

**Proof Outline**:
```coq
Prove auxiliary lemma first:
  Lemma map2_setbit_captures :
    forall mask cand i d,
      nth i cand 0 = d -> d <> 0 ->
      let mask' := map2 setbit_func mask cand in
      Nat.testbit (nth i mask' 0) d = true.

Then prove main theorem:
  By induction on candidates list:
    Base: candidates = []
      iscratch' = iscratch (unchanged)
      Vacuously true

    Step: candidates = cand :: rest
      Assume: IH holds for rest
      Show: adding cand preserves property
        By map2_setbit_captures: cand digits captured
        By IH: rest digits captured
        Therefore: all solution digits captured
```

**Required Lemmas**:
- map2_setbit_correct
- fold_left_monotone_property

---

## 5. Implementation Plan

### Phase 1: Foundation Lemmas (30-45 min)
1. ✓ digit_valid_implies_constraints
2. ✓ find_next_digit_sound
3. ✓ find_next_digit_complete
4. ✓ partial_extends_preserves_validity

### Phase 2: Main Theorems (45-60 min)
5. ✓ enumerate_candidates_aux_sound (using 1, 2)
6. ✓ enumeration_sound (wrapper)
7. ✓ enumerate_candidates_aux_complete (using 3, 4)
8. ✓ enumeration_complete (wrapper)

### Phase 3: Iscratch Update (20-30 min)
9. ✓ map2_setbit_correct
10. ✓ fold_left_accumulation
11. ✓ iscratch_update_sound (using 9, 10)

### Phase 4: Resolve Original Lemmas (60-90 min)
12. ✓ Use proven enumeration to unblock 12 admitted lemmas
13. ✓ Final compilation with zero admits

**Total Estimated Time**: 2.5 - 4 hours

---

## 6. Rocq Proof Tactics Reference

### For Recursive Functions
- `induction fuel` - Strong induction on fuel parameter
- `simpl in H` - Unfold one step of recursion
- `remember (expr) as var` - Name complex expression
- `destruct (match ...) eqn:E` - Case split with equation

### For Boolean Logic
- `andb_true_iff` - Split && into conjuncts
- `orb_true_iff` - Split || into disjuncts
- `Nat.ltb_lt` - Convert < bool to < Prop
- `forallb_forall` - Universal quantification over lists

### For List Properties
- `In_nth` - Element membership via nth
- `nth_In` - nth implies membership (with bounds)
- `app_length` - Length of concatenation
- `fold_left_app` - fold_left distributes over append

### For Arithmetic
- `lia` - Linear integer arithmetic solver
- `Nat.le_antisymm` - Equality from <= both ways
- `Nat.lt_irrefl` - No element < itself

---

## 7. Common Proof Patterns

### Pattern 1: Induction on Fuel + Case Analysis
```coq
induction fuel; intros; simpl.
- (* fuel = 0 *) ...
- (* fuel = S fuel' *)
  destruct (condition) eqn:E.
  + (* true case *) apply IH. ...
  + (* false case *) ...
```

### Pattern 2: Extract from Boolean Conditions
```coq
apply andb_true_iff in H.
destruct H as [H1 H2].
apply Nat.leb_le in H1.
```

### Pattern 3: Fold Left Induction
```coq
induction l as [| hd tl IH]; intros; simpl.
- (* l = [] *) reflexivity.
- (* l = hd :: tl *)
  rewrite IH.
  (* Show property holds after adding hd *)
  ...
```

---

## 8. Risk Assessment

### High Risk Areas
1. **enumerate_complete**: Most complex - requires explicit construction
   - **Mitigation**: Break into smaller lemmas about reachability

2. **Recursion through find_next_digit**: Match doesn't simplify cleanly
   - **Mitigation**: Use `remember` + `rewrite` pattern

3. **fold_left with map2**: Complex nested structure
   - **Mitigation**: Prove map2 properties separately first

### Medium Risk Areas
1. **digit_valid boolean extraction**: Many conjuncts to unpack
2. **Length preservation**: Need careful nth indexing

### Low Risk Areas
1. **enumeration_sound**: Straightforward induction
2. **Helper lemmas**: Mostly boolean logic

---

## 9. Success Criteria

- [ ] All 3 enumeration theorems proven (Qed, not Admitted)
- [ ] All 12 original lemmas resolved
- [ ] SolverSpec.v compiles with 0 Admitted statements
- [ ] All proofs use only standard Rocq tactics (no axioms)
- [ ] Proofs are maintainable (< 50 lines each)

---

## 10. Fallback Strategy

If any proof gets stuck:

1. **Admit the lemma temporarily** - Mark with `(* TODO: ... *)`
2. **Continue with dependent proofs** - Use admitted lemma
3. **Return to stuck proof** - With more context from later work
4. **Ask for architectural changes** - If fundamental issue

**Philosophy**: Progress over perfection in first pass, then iterative refinement.
