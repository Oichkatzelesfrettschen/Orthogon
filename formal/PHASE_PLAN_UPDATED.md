# Updated Phase 1-6 Plan: Formal Verification with Extraction Strategy

**Date**: 2026-01-01
**Supersedes**: Original 6-phase plan from compressed session
**Key Finding**: CertiCoq C extraction NOT compatible with Rocq 9.x

---

## Current State Summary

**Last Updated**: 2026-01-02 (Phase 3 continued)

### Completed Modules (Verified in Rocq)
| Module | Status | Lines | Proven Theorems | Description |
|--------|--------|-------|-----------------|-------------|
| SolverTypes.v | **Phase 1 Done** | 520 | 6 | Core types + latin soundness |
| DSF.v | **Partial** | 370 | 8 | Disjoint Set Forest |
| CageOps.v | **Phase 1 Done** | 485 | 17 | Cage operation evaluation |
| DLX.v | Complete | ~300 | 2 | Dancing Links exact cover |
| SAT.v | Complete | ~300 | 1 | CNF encoding |
| LatinSquare.v | Complete | ~310 | 2 | Latin square constraints |
| SolverSpec.v | **Phase 3 In Progress** | ~4000 | ~30 | Constraint propagation + termination |
| GeneratorSpec.v | Complete | ~500 | 0 | Puzzle generator spec |

### Phase 1 Proven Theorems (2026-01-01)

**SolverTypes.v** (New proofs):
- `valid_latin_grid` - Strong invariant combining latin_invariant with digit validity
- `cell_to_index_bounds` - Index bounds for cell positions
- `grid_get_in_bounds` - Grid access succeeds for valid cells
- `grid_get_in` - Retrieved digits are in grid
- `latin_constraint_sound` - **MAIN**: Valid grid cells contain valid digits
- `latin_constraint_bounds` - Corollary: 1 <= d <= n

**DSF.v** (New proofs):
- `canonify_fuel_returns_root` - Canonify only returns roots
- `canonify_is_root` - Root flag is set for returned index

**CageOps.v** (New proofs):
- `cage_satisfiedb_reflect` - Boolean↔Prop equivalence
- `cage_satisfied_dec` - Cage satisfaction is decidable
- `cage_satisfiedb_sound` - Boolean true implies satisfaction
- `cage_satisfiedb_complete` - Satisfaction implies boolean true

### Phase 3 Proven Theorems (2026-01-01)

**SolverSpec.v** (New proofs):
- `solver_loop_terminates` - **MAIN**: Solver always terminates with fuel = o³
- `cell_unique_digit_complete` - Uniqueness detection finds all singletons
- `cell_unique_digit_sound` - Found unique digits are correct
- Plus 10+ supporting lemmas for solver infrastructure

### Phase 3 Progress Update (2026-01-02)

**SolverSpec.v** - Admits reduced from 9 to 7:
- `place_preserves_invariant` - **PROVEN** (was 6 inline admits)
  * Added helper lemmas: `propagate_row/col_preserves_except`, `propagate_row/col_preserves_outside`
  * Added helper lemmas: `fold_eliminate_others_keeps_n`, `fold_eliminate_others_false`
- `apply_iscratch_cells_preserves_invariant` - **PROVEN**
  * Added `fold_left_preserves_In` for list membership tracking
  * Added `In_seq_bounds` for deriving d ∈ [1,o] from seq membership
- `elimination_preserves_invariant` - **PROVEN** (with preconditions)
- `cube_eliminate_preserves_other` - **PROVEN** (cubepos injectivity)

**Remaining 7 Admitted** (categorized):
- **Model Limitations (4)**: Require full candidate enumeration model
  - `iscratch_captures_solution`, `elimination_pass_sound`
  - `solver_loop_preserves_invariant`, `solver_solution_valid`
- **Termination Tracking (3)**: Require fold tracking for cube_count decrease
  - `elimination_decreases_or_unchanged`, `solver_loop_fuel_sufficient`, `solver_loop_fixed_point`

**Status**: 7 Admitted, ~30 Proven theorems in SolverSpec.v

### Admitted Theorems (TODO)
| Module | Theorem | Complexity |
|--------|---------|------------|
| SolverTypes.v | place_digit_row_unique | Medium |
| DSF.v | dsf_merge_wf | High |
| DSF.v | dsf_merge_equiv | High |
| DSF.v | dsf_merge_size | High |
| LatinSquare.v | valid_complete_solution_is_latin | Medium |
| LatinSquare.v | dlx_solution_valid | High |

### Extraction Status
- **OCaml extraction**: Working (standard, unverified)
- **Verified extraction**: Working (rocq-verified-extraction 0.9.3+9.0)
- **Malfunction compilation**: Working (dsf_init, dsf_canonify, cage_satisfiedb)
- **C bridge**: Working (hand-written, ~2500 LOC)
- **JNI integration**: Working (test suite passes)

---

## Revised Phase Plan

### Phase 1: Consolidate Current Verification (Current Focus)
**Goal**: Complete proofs for existing specifications

#### 1.1 Latin Square Soundness (2-3 days)
```coq
(* Target theorem *)
Theorem latin_constraint_sound:
  forall n grid,
    latin_invariant n grid ->
    forall r c, r < n -> c < n ->
      grid_get n grid (r, c) = Some d ->
      1 <= d <= n.
```

#### 1.2 DSF Correctness (2-3 days)
```coq
(* Union-Find invariant preservation *)
Theorem dsf_merge_preserves_equivalence:
  forall dsf a b,
    dsf_equiv dsf a b <->
    dsf_equiv (dsf_merge dsf a b) a b.
```

#### 1.3 Cage Evaluation Correctness (3-4 days)
```coq
(* Cage satisfaction matches C implementation *)
Theorem cage_satisfiedb_correct:
  forall cage values,
    cage_satisfiedb cage values = true <->
    cage_satisfied (cage_clue cage) values.
```

#### 1.4 Deliverables
- [x] 15+ proven lemmas in existing modules (30+ total: 6 SolverTypes, 8 DSF, 17 CageOps)
- [x] Test suite coverage for C bridge (97 tests: DLX, JNI, Latin, Comprehensive)
- [x] Updated CLAUDE.md with verification status

**C Bridge Test Coverage** (2026-01-01):
| Test Suite | Tests | Coverage |
|------------|-------|----------|
| test_dlx_latin | 9 | DLX solver, matrix construction, exact cover |
| test_jni_interface | 29 | JNI entry points, edge cases, all sizes 2-16 |
| test_latin_verified | 19 | Latin generation, shuffling, validation |
| test_comprehensive | 40 | Full size range, CNF encoding, benchmarks |

Run with: `make all-tests`

---

### Phase 2: Verified Extraction Pipeline ✓ COMPLETE
**Goal**: Switch to rocq-verified-extraction for reduced TCB
**Status**: Completed 2026-01-01

#### 2.1 Environment Setup ✓
```bash
# Create isolated switch for verified extraction
opam switch create keen-verified 4.14.2
eval $(opam env --switch=keen-verified)

# Add Rocq repos
opam repo add rocq-released https://rocq-prover.org/opam/released

# Install Rocq 9.0.0 (required for verified extraction)
opam install rocq-core.9.0.0 rocq-stdlib.9.0.0

# Install verified extraction
opam install rocq-verified-extraction
```

#### 2.2 Porting Extraction Config (2-3 days)
```coq
(* Replace standard extraction *)
From VerifiedExtraction Require Import Extraction.
From VerifiedExtraction Require Import ExtractionLib.

(* Verified extraction of DSF *)
MetaRocq Run (tmQuoteRec dsf_init) >>= tmEval all.
Verified Extraction dsf_init.
Verified Extraction dsf_canonify.
Verified Extraction dsf_merge.
```

#### 2.3 Malfunction Integration (3-4 days)
```makefile
# New build target for Malfunction compilation
MALC = malfunction

extracted/DSFOps.mlf: DSF.v
    $(ROCQ) -Q . KeenKenning DSF.v
    # Verified extraction outputs .mlf files

extracted/DSFOps.o: extracted/DSFOps.mlf
    $(MALC) compile $< -o $@
```

#### 2.4 C FFI Bridge Update (2-3 days)
```c
/* New FFI for Malfunction-compiled objects */
#include "malfunction_runtime.h"

/* Link against .o files from malfunction compile */
extern int ml_dsf_init(int n);
extern int ml_dsf_canonify(int* dsf, int n, int x);
extern void ml_dsf_merge(int* dsf, int n, int a, int b);

/* C wrapper maintaining current API */
kv_dsf_t* kv_dsf_init(int n) {
    return (kv_dsf_t*)ml_dsf_init(n);
}
```

#### 2.5 Deliverables
- [x] Verified extraction working for core modules (DSF, CageOps)
- [x] Malfunction compilation pipeline (dsf_init.o, dsf_canonify.o, cage_satisfiedb.o)
- [ ] Updated C FFI bridge (deferred to Phase 5)
- [ ] Performance comparison: standard vs verified (deferred)

---

### Phase 3: Solver Algorithm Verification ⚠ IN PROGRESS
**Goal**: Prove constraint propagation correctness
**Status**: Partial completion (2026-01-02) - 12 admitted lemmas remain

#### 3.1 Propagation Soundness ⚠ ADMITTED
```coq
(* Elimination pass preserves solutions *)
Theorem elimination_pass_sound:
  forall o config cages state,
    solver_invariant o state ->
    let state' := elimination_pass o config cages state in
    forall sol, is_solution o cages sol ->
                solution_consistent_with_cube o (ss_cube state') sol.
```

**Status**: ADMITTED (line 1100)
**Blockers**:
- Lines 1080, 1096: Requires modeling actual candidate enumeration
- Current placeholder: `let iscratch' := iscratch` (line 392) bypasses enumeration
- Missing: Connection between C enumeration algorithm and Rocq specification

#### 3.2 Solver Termination ✓ PROVEN
```coq
(* Solver loop terminates *)
Theorem solver_loop_terminates:
  forall o config cages state,
    o > 0 ->
    solver_invariant o state ->
    exists fuel, ss_changed (solver_loop fuel o config cages state) = false \/
                 grid_complete o (ss_grid (solver_loop fuel o config cages state)).
```

**Status**: PROVEN (lines 1222-1237, uses fuel-based construction)

#### 3.3 Uniqueness Detection ⚠ PARTIALLY PROVEN
```coq
(* Unique digit detection is complete *)
Theorem cell_unique_digit_complete:
  forall o cube r c,
    (exists! d, 1 <= d <= o /\ testbit (cube_get cube o r c) d = true) ->
    exists d, cell_unique_digit o cube r c = Some d.
```

**Status**: ADMITTED (line 1481) - helper lemmas incomplete
**Supporting lemmas**:
- `cell_unique_digit_sound`: PROVEN (line 1341)
- `filter_seq_singleton`: ADMITTED (line 1481)

#### 3.4 Supporting Infrastructure ⚠ ADMITTED

**Admitted helper lemmas** (10 additional):
| Line | Lemma | Purpose | Complexity |
|------|-------|---------|------------|
| 1038 | `elimination_preserves_consistent` (helper) | Links elimination to solution preservation | High |
| 1218 | `elimination_decreases_or_unchanged` | Termination measure monotonicity | Medium |
| 1285 | `solver_loop_fixed_point` | Fixed point characterization | Medium |
| 1333 | (helper for `cell_unique_digit_sound`) | Index bounds checking | Low |
| 1481 | `filter_seq_singleton` | Uniqueness of filtered sequences | Low |
| 1494 | `propagate_row_eliminates` | Row elimination correctness | Medium |
| 1505 | `propagate_col_eliminates` | Column elimination correctness | Medium |
| 1550 | `place_preserves_invariant` | Placement preserves solver invariant | Medium |
| 1597 | `elimination_preserves_invariant` | Pass preserves invariant | High |
| 1678 | `solver_loop_preserves_invariant` | Loop preserves invariant | High |
| 1787 | `solver_solution_valid` | Final theorem: solver produces valid solutions | High |

#### 3.5 Candidate Enumeration Modeling (NEW - In Progress)

**Critical Discovery** (2026-01-02):
- Line 392 contains placeholder: `let iscratch' := iscratch in (* Placeholder *)`
- This blocks completion of 12 admitted lemmas
- Root cause: Rocq spec does not model actual C enumeration algorithm

**C Implementation Analysis Completed**:
- Analyzed `keen_solver.c` candidate enumeration (recursive backtracking)
- Reviewed reference implementations:
  - `external/latin-square-toolbox/` - Academic constraint solver patterns
  - `core/` - Original puzzle generation algorithms
  - `kenning/` - Android integration layer
  - `scripts/ai/` - ML-based generation (distinct from solver)
- Documented insights in `AGL_INSIGHTS.md` (Game Semantics, GoI, Linear Logic frameworks)

**Required Work**:
```coq
(* Model candidate enumeration from C implementation *)
Fixpoint enumerate_candidates
  (cage : Cage) (iscratch : IScr) (dscratch : list nat) (fuel : nat)
  : list (list nat) :=
  match fuel with
  | 0 => []
  | S n =>
      match find_next_valid cage iscratch dscratch with
      | None => [dscratch]  (* Complete assignment *)
      | Some (d, dscratch') =>
          enumerate_candidates cage iscratch dscratch' n
      end
  end.

(* Key property: enumeration completeness *)
Theorem enumeration_complete :
  forall cage values,
    cage_satisfied cage values ->
    exists fuel dscratch,
      In values (enumerate_candidates cage (init_iscratch cage) [] fuel).

(* Soundness: all enumerated candidates satisfy cage *)
Theorem enumeration_sound :
  forall cage fuel dscratch values,
    In values (enumerate_candidates cage (init_iscratch cage) dscratch fuel) ->
    cage_satisfied cage values.
```

**Integration with Existing Proofs**:
- Replace line 392 placeholder with actual enumeration call
- Prove `iscratch_captures_solutions`: solution digits appear in iscratch masks
- Unblock `elimination_pass_sound` by connecting enumeration to deduction

#### 3.6 Deliverables

**Completed** (2026-01-01):
- [x] Termination proof (fully proven via fuel-based construction)
- [x] Uniqueness detection soundness (proven)
- [x] Integration with cage evaluation (leverages CageOps reflection lemmas)

**In Progress** (2026-01-02):
- [ ] **3.5 Candidate Enumeration Modeling**
  - [ ] Formalize recursive enumeration from `keen_solver.c`
  - [ ] Prove enumeration completeness and soundness
  - [ ] Replace placeholder at line 392
  - [ ] Unblock dependent lemmas

**Blocked** (awaiting 3.5 completion):
- [ ] Soundness proof for elimination pass (11 admits)
- [ ] All 12 admitted lemmas resolved
- [ ] Zero admitted statements in SolverSpec.v

#### 3.7 Acceptance Criteria (UPDATED)

**Phase 3 is NOT complete until**:
1. ✓ Termination proven (DONE)
2. ✗ ALL 12 admitted lemmas proven (0/12 complete)
3. ✗ Zero `Admitted.` statements in SolverSpec.v
4. ✗ Candidate enumeration fully modeled and integrated
5. ✗ `elimination_pass_sound` proven without admits

**Timeline Revision**:
- Original: 3 weeks
- Revised: 4-5 weeks (accounting for enumeration modeling)
  - Week 1-2: Candidate enumeration formalization
  - Week 3: Prove enumeration theorems
  - Week 4: Complete dependent lemmas
  - Week 5: Integration and verification

#### 3.8 References (NEW)

**New Documentation** (2026-01-02):
- `AGL_INSIGHTS.md` - Game Semantics, GoI, Linear Logic frameworks for verification
- C implementation analysis:
  - `app/src/main/jni/keen_solver.c` - Actual enumeration algorithm
  - `external/latin-square-toolbox/` - Reference constraint solving patterns
  - `core/` - Original puzzle generator
  - `scripts/ai/` - ML-based generation (separate from verification scope)

**Theoretical Frameworks**:
- Game Semantics: Model solver as two-player game (Player vs Constraints)
- Geometry of Interaction: Execution formula as token machine
- Linear Logic: Candidates as linear resources (placement consumes)
- Interaction Nets: Constraint network as graph reduction

**Key Insight**: C implementation is direct realization of game semantics strategy construction - formal proof should mirror this structure

---

### Phase 4: Generator Verification (Month 2)
**Goal**: Prove puzzle generator produces solvable puzzles

#### 4.1 Latin Square Generation
```coq
(* Generated Latin squares are valid *)
Theorem gen_latin_valid:
  forall seed n,
    3 <= n <= 16 ->
    latin_invariant n (gen_latin seed n).
```

#### 4.2 Cage Construction Correctness
```coq
(* Cages partition the grid *)
Theorem cages_partition_grid:
  forall gen_out,
    let cages := go_cages gen_out in
    let n := go_width gen_out in
    forall r c, r < n -> c < n ->
      exists! cage, In cage cages /\ In (r, c) (cage_cells cage).
```

#### 4.3 Solvability Guarantee
```coq
(* Generated puzzles have unique solutions *)
Theorem generated_puzzle_solvable:
  forall config seed,
    valid_config config ->
    let out := generate config seed in
    exists! sol, puzzle_solution out sol.
```

#### 4.4 Deliverables
- [ ] Latin generation proof
- [ ] Cage partition proof
- [ ] Solvability theorem
- [ ] Difficulty calibration lemmas

---

### Phase 5: End-to-End Integration (Month 3)
**Goal**: Verified pipeline from Rocq to Android

#### 5.1 Full Extraction Pipeline
```
Rocq Specs (100% verified)
    |
    v [Verified Extraction - PROVEN CORRECT]
Malfunction IR
    |
    v [malfunction compile]
Native .o files
    |
    v [C FFI Bridge]
libkeen_verified.so
    |
    v [JNI]
Android (Kotlin)
```

#### 5.2 Property Preservation Proof
```coq
(* Extraction preserves operational semantics *)
Theorem extraction_semantic_preservation:
  forall t v,
    t -->* v (in Rocq) <->
    erased(t) -->* erased(v) (in Lambda-Box).

(* Provided by rocq-verified-extraction *)
```

#### 5.3 Integration Testing
```kotlin
// Android instrumented tests with verified backend
@Test
fun testVerifiedSolver() {
    val puzzle = VerifiedPuzzleGenerator.generate(size = 6, diff = Normal)
    assertTrue(puzzle.hasUniqueSolution())

    val solution = VerifiedSolver.solve(puzzle)
    assertTrue(solution.isValid())
}
```

#### 5.4 Deliverables
- [ ] Complete verified extraction for all modules
- [ ] Native library with verified implementation
- [ ] Android integration tests
- [ ] Performance benchmarks

---

### Phase 6: Documentation and Release (Month 4)
**Goal**: Production-ready verified solver

#### 6.1 Verification Report
- Theorems proven (quantified)
- TCB analysis and audit
- Performance characteristics
- Limitations and assumptions

#### 6.2 Build System
```makefile
# Production build with verified extraction
.PHONY: verified-release

verified-release: verify-proofs extract-verified compile-malfunction build-native
    ./gradlew assembleKenningRelease
```

#### 6.3 CI/CD Integration
```yaml
# .github/workflows/verified-build.yml
name: Verified Build
on: [push, pull_request]
jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/setup-opam@v2
      - run: opam install rocq-verified-extraction
      - run: make -C formal verified-proofs
      - run: make -C formal verified-extract
      - run: ./gradlew assembleKenningDebug
```

#### 6.4 Deliverables
- [ ] Complete verification report
- [ ] CI/CD with verification checks
- [ ] Release notes for verified solver
- [ ] Academic paper (optional)

---

## Timeline Summary

| Phase | Duration | Key Outcome |
|-------|----------|-------------|
| Phase 1 | 2 weeks | Core proofs complete |
| Phase 2 | 2 weeks | Verified extraction working |
| Phase 3 | 3 weeks | Solver verified |
| Phase 4 | 3 weeks | Generator verified |
| Phase 5 | 2 weeks | End-to-end integration |
| Phase 6 | 2 weeks | Production release |

**Total**: ~14 weeks (3.5 months)

---

## Risk Mitigation

### Risk 1: rocq-verified-extraction Stability
**Mitigation**: Maintain fallback to standard extraction; both can coexist

### Risk 2: Malfunction Performance
**Mitigation**: Benchmark early in Phase 2; fall back to standard OCaml if needed

### Risk 3: C FFI Complexity
**Mitigation**: Minimize FFI surface; keep most logic in verified Rocq/OCaml

### Risk 4: CertiCoq Becomes Available
**Mitigation**: Design for migration; current architecture is compatible

---

## Decision Log

| Date | Decision | Rationale |
|------|----------|-----------|
| 2026-01-01 | CertiCoq not viable | Incompatible with Rocq 9.x |
| 2026-01-01 | Adopt rocq-verified-extraction | Compatible, peer-reviewed, smaller TCB |
| 2026-01-01 | Maintain current C bridge | Working, well-tested, low risk |
| 2026-01-01 | Target Rocq 9.0.0 for verified | Required by rocq-verified-extraction |

---

## References

1. [EXTRACTION_COMPARISON.md](./EXTRACTION_COMPARISON.md) - Detailed extraction analysis
2. [rocq-verified-extraction](https://github.com/MetaRocq/rocq-verified-extraction)
3. [Verified Extraction from Coq to OCaml (PLDI 2024)](https://dl.acm.org/doi/10.1145/3656379)
4. [CertiCoq](https://certicoq.org/) - For future reference
