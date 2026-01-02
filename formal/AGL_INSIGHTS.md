# AGL Game Geometry Documentation - Insights for Constraint Verification

**Date**: 2026-01-02
**Purpose**: Apply advanced theoretical frameworks (Game Semantics, GoI, Linear Logic) to KenKen solver verification

---

## Document Collection Summary

Located at: `/home/eirikr/Documents/AGL_Library/Game_Geometry_Documentation/`

**Key Topics**: 45+ research papers on:
- Game Semantics and Game Models
- Geometry of Interaction (GoI)
- Interaction Nets and Combinators
- Linear Logic and Differential λ-Calculus
- Ludics and Abstract Machines

---

## 1. Game Semantics for Constraint Satisfaction

**Core Concept:** Model solver as two-player game:
- **Player (Solver):** Chooses digit placements
- **Opponent (Constraints):** Accepts or rejects based on Latin/cage rules

### Rocq Encoding

```coq
(* Coinductive game tree *)
CoInductive SolverGame : Type :=
  | SolverMove : Cell -> nat -> (bool -> SolverGame) -> SolverGame
  | ConstraintCheck : Puzzle -> Grid -> SolverGame.

(* Winning strategy = finding valid solution *)
Definition winning_strategy (g : SolverGame) : Prop :=
  exists moves : list (Cell * nat),
    all_moves_valid moves /\ leads_to_solution g moves.

(* Solver as winning strategy construction *)
Inductive SolverStrategy : SolverState -> Prop :=
  | solved : forall s, is_solution s -> SolverStrategy s
  | search : forall s c d,
      valid_move s c d ->
      SolverStrategy (place_digit s c d) ->
      SolverStrategy s.

Theorem solver_finds_strategy :
  forall puzzle,
    solvable puzzle ->
    exists strategy, SolverStrategy (init_state puzzle).
```

**Application:** Backtracking = exploring losing branches until finding winning strategy

**Key Theorems:**
- Determinacy: Either Player or Opponent has winning strategy
- Soundness: Winning strategy yields valid solution
- Completeness: Solvable puzzle has winning strategy

---

## 2. Interaction Nets for Constraint Propagation

**Core Concept:** Constraint network as interaction system:
- **Nodes:** Cells, cages, row/column constraints
- **Edges:** Dependencies (cell value affects row/column availability)
- **Reduction:** Propagation eliminates possibilities

### Rocq Encoding

```coq
Inductive ConstraintNode : Type :=
  | CellNode : Cell -> ConstraintNode
  | RowConstraint : nat -> ConstraintNode
  | ColConstraint : nat -> ConstraintNode
  | CageConstraint : Cage -> ConstraintNode.

(* Interaction rules *)
Inductive PropagationRule : ConstraintNode -> ConstraintNode -> Prop :=
  | cell_to_row : forall c d,
      CellNode c → RowConstraint (fst c) ⊢ eliminate d
  | cell_to_col : forall c d,
      CellNode c → ColConstraint (snd c) ⊢ eliminate d.

(* Propagation as graph rewriting *)
Fixpoint propagate_constraints (fuel : nat) (graph : ConstraintGraph) : ConstraintGraph :=
  match fuel with
  | 0 => graph
  | S n => propagate_constraints n (apply_rules graph)
  end.

Theorem propagation_confluent :
  forall graph n m,
    n >= sufficient_fuel graph ->
    m >= sufficient_fuel graph ->
    propagate_constraints n graph = propagate_constraints m graph.
```

**Application:** Models cube elimination as graph reduction

**Key Properties:**
- Confluence: Order of reductions doesn't matter
- Termination: Fixed point always reached
- Soundness: Reductions preserve solutions

---

## 3. Geometry of Interaction (GoI) for Execution

**Core Concept:** Execution formula as token machine:
- **State:** Current partial grid + cube
- **Tokens:** Candidate digits flowing through constraints
- **Normalization:** Reaching fixed point (no more eliminations)

### Rocq Encoding

```coq
(* GoI-style execution *)
Fixpoint execute_propagation (fuel : nat) (state : SolverState) : SolverState :=
  match fuel with
  | 0 => state
  | S n =>
      let state' := single_propagation_step state in
      if state_eq state state'
      then state  (* Fixed point *)
      else execute_propagation n state'
  end.

Lemma propagation_terminates :
  forall state, exists n,
    execute_propagation n state = execute_propagation (S n) state.

Lemma normalization_unique :
  forall state n m,
    execute_propagation n state = execute_propagation (S n) state ->
    execute_propagation m state = execute_propagation (S m) state ->
    execute_propagation n state = execute_propagation m state.
```

**Application:** Formalizes solver loop termination and fixed-point convergence

**Key Results:**
- Strong normalization: Always terminates
- Uniqueness: Fixed point is unique
- Correctness: Normal form is maximal constraint propagation

---

## 4. Linear Logic for Resource Management

**Core Concept:** Candidates as linear resources:
- **!digit:** Unlimited digit availability (before constraints)
- **digit ⊗ digit:** Placement consumes resource in row AND column
- **digit ⊸ ⊥:** Constraint rejects digit

### Rocq Encoding

```coq
(* Linear type for digit placement *)
Inductive Placement : Type :=
  | Available : nat -> Placement  (* !digit *)
  | Used : nat -> Cell -> Placement  (* digit consumed *)
  | Excluded : nat -> Cell -> Placement.  (* digit ⊸ ⊥ *)

(* Linear logic sequent for valid placement *)
Definition valid_placement (cube : Cube) (c : Cell) (d : nat) : Prop :=
  cube c d = true /\  (* Resource available *)
  forall c', conflicts c c' -> cube c' d = true -> c <> c'.  (* Linear use *)

(* Latin square = linear use of digits *)
Definition latin_square (grid : Grid) : Prop :=
  (forall r d, count_in_row grid r d <= 1) /\
  (forall c d, count_in_col grid c d <= 1).

(* Proved via linear logic resource accounting *)
Lemma placement_preserves_linearity :
  forall grid c d,
    latin_square grid ->
    valid_placement grid c d ->
    latin_square (place grid c d).
```

**Application:** Ensures no double-use of digits (Latin property)

**Key Insights:**
- Multiplicative: Placing digit consumes row AND column resources
- Exponential: Multiple cages can read same digit (!-modality)
- Cut-elimination: Constraint propagation = proof normalization

---

## 5. Differential Lambda Calculus for Sensitivity Analysis

**Core Concept:** How small changes propagate:
- Placing one digit triggers cascade of eliminations
- Derivative = constraint sensitivity

### Rocq Encoding

```coq
(* Sensitivity: how many cells affected by placement *)
Definition propagation_impact (state : SolverState) (c : Cell) (d : nat) : nat :=
  let state' := place_digit state c d in
  count_changed_cells (ss_cube state) (ss_cube state').

(* Bounded propagation *)
Lemma propagation_bounded :
  forall state c d,
    propagation_impact state c d <= 2 * (ss_order state).

(* Compositional sensitivity *)
Lemma propagation_compositional :
  forall state c1 d1 c2 d2,
    disjoint_cells c1 c2 ->
    propagation_impact (place_digit state c1 d1) c2 d2 <=
    propagation_impact state c2 d2.
```

**Application:** Analyzes cascading eliminations and proves bounded impact

---

## 6. Practical Recommendations for Rocq Modeling

### A. Candidate Enumeration as Game Strategy

```coq
(* Model enumeration as constructing winning strategy *)
Fixpoint enumerate_candidates
  (cage : Cage) (iscratch : IScr) (dscratch : list nat) (fuel : nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S n =>
      match find_next_valid cage iscratch dscratch with
      | None => [dscratch]  (* Complete assignment *)
      | Some (d, dscratch') =>
          (* Explore branch *)
          enumerate_candidates cage iscratch dscratch' n
      end
  end.

Theorem enumeration_complete :
  forall cage values,
    cage_satisfied cage values ->
    exists fuel dscratch,
      In values (enumerate_candidates cage (init_iscratch cage) [] fuel).
```

### B. Constraint Propagation as Interaction Net Reduction

```coq
(* Single reduction step *)
Definition reduce_constraint (cube : Cube) (c : Cell) (d : nat) : Cube :=
  eliminate_row cube (fst c) d ∘ eliminate_col cube (snd c) d.

(* Iterated reduction until fixed point *)
Fixpoint reduce_until_fixpoint (fuel : nat) (cube : Cube) : Cube :=
  match fuel with
  | 0 => cube
  | S n =>
      let cube' := apply_all_constraints cube in
      if cube_eq cube cube'
      then cube
      else reduce_until_fixpoint n cube'
  end.

Theorem reduction_sound :
  forall cube solution,
    solution_satisfies cube solution ->
    solution_satisfies (reduce_until_fixpoint (cube_size cube) cube) solution.
```

### C. Termination via GoI Normalization

```coq
(* Measure for termination: cube possibilities decrease *)
Definition cube_measure (cube : Cube) : nat :=
  count_true_bits cube.

Lemma propagation_decreases :
  forall cube,
    cube_not_empty cube ->
    let cube' := single_propagation_step cube in
    cube_measure cube' < cube_measure cube \/ cube' = cube.

Theorem solver_terminates_goi :
  forall state,
    exists n,
      solver_loop n state = solver_loop (S n) state.
Proof.
  intros. exists (cube_measure (ss_cube state)).
  apply well_founded_induction with (R := lt) (a := cube_measure (ss_cube state)).
  - apply Nat.lt_wf_0.
  - intros. destruct (cube_eq (ss_cube x) (ss_cube (single_step x))).
    + reflexivity.
    + apply propagation_decreases.
Qed.
```

---

## 7. Key Theorems to Prove (Framework-Guided)

### Termination (GoI Normalization)

```coq
Theorem solver_terminates :
  forall state,
    exists n, solver_loop n state = solver_loop (S n) state.
```

**Proof Strategy:** Well-founded induction on `cube_measure`

### Soundness (Game Semantics Winning Condition)

```coq
Theorem solver_sound :
  forall state solution,
    solver_returns state = Some solution ->
    is_valid_solution solution.
```

**Proof Strategy:** Induction on solver strategy construction

### Completeness (Interaction Net Confluence)

```coq
Theorem solver_complete :
  forall puzzle solution,
    is_solution puzzle solution ->
    exists fuel, solver_loop fuel (init_state puzzle) = Success solution.
```

**Proof Strategy:** Show constraint graph has unique normal form

### Constraint Propagation Soundness (Linear Logic Cut Elimination)

```coq
Theorem propagation_sound :
  forall state,
    let state' := propagate state in
    forall sol, satisfies state' sol -> satisfies state sol.
```

**Proof Strategy:** Linear resource preservation

---

## 8. Comparison: Theoretical Framework vs C Implementation

| Aspect | Theoretical Model | C Implementation |
|--------|------------------|------------------|
| **Backtracking** | Game tree exploration | Recursive loop with dscratch[] |
| **Propagation** | Interaction net reduction | Cube elimination via bitwise ops |
| **Termination** | GoI normalization | Fuel bound (o³) |
| **Latin Property** | Linear logic resources | Row/column boolean arrays |
| **Cage Constraints** | Opponent rejections | C_ADD/C_MUL arithmetic checks |

**Key Insight:** C implementation is direct realization of game semantics strategy construction

---

## 9. Integration with Existing Rocq Specs

### SolverSpec.v Enhancement

```coq
(* Add game semantics layer *)
Section GameSemantics.

Variable o : nat.

(* Game state *)
Record GameState := {
  gs_solver_state : SolverState o;
  gs_player_move : option (Cell * nat);
  gs_opponent_response : bool
}.

(* Game dynamics *)
Inductive game_step : GameState -> GameState -> Prop :=
  | player_places : forall s c d,
      valid_move (gs_solver_state s) c d ->
      game_step s {| gs_solver_state := place_digit (gs_solver_state s) c d;
                     gs_player_move := Some (c, d);
                     gs_opponent_response := true |}
  | opponent_rejects : forall s c d,
      ~valid_move (gs_solver_state s) c d ->
      game_step s {| gs_solver_state := gs_solver_state s;
                     gs_player_move := Some (c, d);
                     gs_opponent_response := false |}.

(* Winning condition *)
Definition player_wins (s : GameState) : Prop :=
  is_solution o (ss_grid (gs_solver_state s)).

Theorem solver_constructs_winning_strategy :
  forall puzzle,
    solvable o puzzle ->
    exists strategy : list (Cell * nat),
      player_wins (execute_strategy puzzle strategy).

End GameSemantics.
```

---

## 10. Next Steps

1. **Model candidate enumeration** using game semantics framework
2. **Prove termination** via GoI normalization measure
3. **Prove soundness** via linear logic resource preservation
4. **Prove completeness** via interaction net confluence
5. **Extract verified code** to Malfunction/C

---

## References

### Primary Sources
- `/home/eirikr/Documents/AGL_Library/Game_Geometry_Documentation/`
  - `game_models_computation.pdf`
  - `game_based_verification.pdf`
  - `geometry_interaction_intro.pdf`
  - `interaction_nets_intro.pdf`
  - `goi_linear_logic.pdf`

### Related Work
- Abramsky & McCusker: Game Semantics (Full Abstraction)
- Girard: Geometry of Interaction (Execution Formula)
- Lafont: Interaction Nets (Graph Rewriting)
- Girard: Linear Logic (Resource Semantics)

### Project Context
- `PHASE_PLAN_UPDATED.md` - Overall verification roadmap
- `SolverSpec.v` - Current solver specification (839 lines, 13 theorems)
- `keen_solver.c` - C implementation analysis
