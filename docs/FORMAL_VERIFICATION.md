# Formal Verification Architecture

**Generated:** 2026-01-01
**Purpose:** Document formal methods integration for DLX+SAT hybrid solver

---

## Executive Summary

This document describes the formal verification approach for the KeenKenning
solver, using Coq for algorithm correctness and Z3 for constraint solving.
The goal is to extract verified C code from proven specifications.

---

## Tool Chain

| Tool | Version | Purpose |
|------|---------|---------|
| Rocq (Coq) | 9.1.0 | Proof assistant, verified extraction |
| Z3 | 4.15.4 | SMT solver for cage constraints |
| OCaml | (extraction target) | Intermediate from Coq |
| cloc | - | Lines of code analysis |
| lizard | - | Cyclomatic complexity |
| cscope | - | C source navigation |

---

## File Structure

```
formal/
├── LatinSquare.v           # Coq: Latin square + exact cover spec
├── DLX.v                   # Coq: Dancing Links algorithm spec
├── SAT.v                   # Coq: CNF encoding spec
├── Extraction.v            # Coq: OCaml extraction config
├── LatinSquareSMT.smt2     # Z3: Parameterized constraint encoding
├── LatinSquare4x4.smt2     # Z3: Concrete 4x4 example (validated)
├── z3_cage_solver.h        # C: Z3 integration header (future)
├── keen_verified.h         # C: Verified functions API
├── keen_verified.c         # C: Coq-translated implementation
├── dlx_latin_bridge.h      # C: DLX integration bridge API
├── dlx_latin_bridge.c      # C: Bridge implementation
├── latin_verified.h        # C: Latin generator wrapper API
├── latin_verified.c        # C: Latin generator implementation
├── keen_verified_jni.h     # C: JNI-compatible interface
├── keen_verified_jni.c     # C: JNI implementation
├── test_dlx_latin.c        # Test: Basic DLX integration (9 tests)
├── test_comprehensive.c    # Test: All grid sizes (40 tests)
├── test_latin_verified.c   # Test: Latin generator (29 tests)
├── test_jni_interface.c    # Test: JNI interface (19 tests)
├── Makefile                # Build system
├── DLX.ml/mli              # Extracted OCaml
├── LatinSquare.ml/mli      # Extracted OCaml
└── SAT.ml/mli              # Extracted OCaml
```

---

## Coq Specification (LatinSquare.v)

### Core Definitions

```coq
(** Cell position *)
Definition Cell := (nat * nat)%type.

(** Grid assignment *)
Definition Grid (n : nat) := Cell -> option nat.

(** Latin square validity *)
Definition is_latin_square (n : nat) (g : Grid n) : Prop :=
  n > 0 /\ complete n g /\ row_unique n g /\ col_unique n g.
```

### Exact Cover Encoding

A Latin square can be encoded as an exact cover problem with three constraint types:
1. **CellFilled(r, c)**: Cell (r,c) has exactly one value
2. **RowValue(r, v)**: Row r contains value v exactly once
3. **ColValue(c, v)**: Column c contains value v exactly once

For an NxN grid:
- **Rows in matrix**: N³ (each possible placement)
- **Columns in matrix**: 3N² (cell + row-value + col-value constraints)

### DLX Algorithm Specification

```coq
Record DLXNode := mkNode {
  node_left : nat;
  node_right : nat;
  node_up : nat;
  node_down : nat;
  node_col : nat;
  node_row : nat
}.

Record DLXState := mkState {
  nodes : list DLXNode;
  header : nat;
  solution : list nat;
  col_sizes : list nat
}.
```

### Main Theorems

1. **valid_complete_solution_is_latin**: A valid, complete placement solution
   corresponds to a valid Latin square.

2. **dlx_solution_valid**: A DLX exact cover solution yields a valid placement
   solution with N² placements.

3. **cover_uncover_inverse** (axiom): Cover and uncover operations are inverses,
   preserving the DLX node structure.

### Extraction

```coq
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extract Inductive nat => "int" [ "0" "succ" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
```

---

## Z3 SMT Encoding (LatinSquareSMT.smt2)

### Variable Encoding

For an NxN grid, use function `(cell r c)` returning value at (r, c).

### Constraints

```smt2
; Value range
(assert (forall ((r Int) (c Int))
  (=> (valid-cell r c)
      (and (>= (cell r c) 1) (<= (cell r c) N)))))

; Row uniqueness (using distinct for concrete encoding)
(assert (distinct cell_0_0 cell_0_1 cell_0_2 cell_0_3))

; Column uniqueness
(assert (distinct cell_0_0 cell_1_0 cell_2_0 cell_3_0))
```

### Cage Constraints

| Operation | SMT Encoding |
|-----------|-------------|
| ADD | `(= (+ c1 c2 ...) target)` |
| SUB | `(or (= (- c1 c2) target) (= (- c2 c1) target))` |
| MUL | `(= (* c1 c2 ...) target)` |
| DIV | `(or (= (* c2 target) c1) (= (* c1 target) c2))` |
| XOR | `(= (bvxor ...) target)` |
| MOD | `(= (mod (+ c1 c2 ...) N) target)` |

### Killer Mode

```smt2
(define-fun killer-3 ((r1 c1) (r2 c2) (r3 c3)) Bool
  (and (not (= (cell r1 c1) (cell r2 c2)))
       (not (= (cell r1 c1) (cell r3 c3)))
       (not (= (cell r2 c2) (cell r3 c3)))))
```

---

## Hybrid DLX+SAT Architecture

### Decision Flow

```
Input: Cage configuration
    |
    v
Calculate max_tuples = N^cage_size
    |
    v
┌───────────────────────────────────────────────┐
│ max_tuples < 100?  → Enumerate all tuples     │
│ max_tuples < 500?  → Use DLX with pruning     │
│ max_tuples < 1000? → Use Z3/SAT solver        │
│ max_tuples >= 2000? → Regenerate cages        │
└───────────────────────────────────────────────┘
    |
    v
Output: Valid placements for cage
```

### Threshold Rationale

| Threshold | Value | Reason |
|-----------|-------|--------|
| SMALL | 100 | Enumeration is O(100) - trivial |
| DLX | 500 | DLX overhead justified |
| SAT | 1000 | Z3 startup amortized |
| ABORT | 2000 | Diminishing returns, retry |

### Example Calculations

| Grid | Cage Size | Max Tuples | Decision |
|------|-----------|------------|----------|
| 4x4 | 2 | 16 | Enumerate |
| 6x6 | 3 | 216 | DLX |
| 9x9 | 4 | 6561 | SAT |
| 16x16 | 5 | 1,048,576 | Abort/Retry |

---

## C Integration (z3_cage_solver.h)

### API Summary

```c
// Create solver context
Z3CageSolverCtx *z3_cage_solver_new(int grid_size);

// Add constraints
bool z3_add_latin_constraints(Z3CageSolverCtx *ctx);
bool z3_add_cage_constraint(Z3CageSolverCtx *ctx, const CageConstraint *cage);
bool z3_add_fixed_cell(Z3CageSolverCtx *ctx, int row, int col, int value);

// Solve
bool z3_check_sat(Z3CageSolverCtx *ctx);
bool z3_get_solution(Z3CageSolverCtx *ctx, int *grid);

// Uniqueness check
bool z3_has_unique_solution(Z3CageSolverCtx *ctx);
```

### Build Integration

```cmake
# Optional Z3 integration
find_package(Z3 QUIET)
if(Z3_FOUND)
    target_compile_definitions(keen-solver PRIVATE KEEN_USE_Z3)
    target_link_libraries(keen-solver PRIVATE z3)
endif()
```

---

## Verification Status

| Component | Specification | Proof | Extraction | Integration |
|-----------|--------------|-------|------------|-------------|
| Latin Square | ✓ Complete | ⚠ Admitted | ✓ Complete | ✓ C impl |
| Exact Cover | ✓ Complete | ⚠ Admitted | ✓ Complete | ✓ C impl |
| DLX Algorithm | ✓ Complete | ⚠ Axiom | ✓ Complete | ✓ Bridge |
| SAT Encoding | ✓ Complete | ✓ Partial | ✓ Complete | ✓ C impl |
| Cage Constraints | ✓ Complete | N/A (SMT) | N/A | ✓ C impl |
| Latin Generator | ✓ Complete | ✓ Verified | ✓ Complete | ✓ Wrapper |
| JNI Interface | N/A | N/A | N/A | ✓ Complete |
| Z3 Integration | ✓ Header | N/A | N/A | ⏳ Pending |

### Extracted Files (2026-01-01)

| File | Size | Purpose |
|------|------|---------|
| `DLX.ml` | 3.1k | Exact cover checking |
| `DLX.mli` | 877B | OCaml interface |
| `LatinSquare.ml` | 5.3k | Latin square definitions |
| `LatinSquare.mli` | 1.3k | OCaml interface |
| `SAT.ml` | 27k | CNF encoding |
| `SAT.mli` | 3.3k | OCaml interface |

### C Implementation

| File | Lines | Purpose |
|------|-------|---------|
| `keen_verified.h` | 219 | Verified functions API |
| `keen_verified.c` | 330 | Coq-translated implementation |
| `dlx_latin_bridge.h` | 78 | DLX integration API |
| `dlx_latin_bridge.c` | 275 | Bridge to dlx.c solver |
| `latin_verified.h` | 82 | Latin generator API |
| `latin_verified.c` | 170 | Generator wrapper |
| `keen_verified_jni.h` | 120 | JNI-compatible API |
| `keen_verified_jni.c` | 130 | JNI implementation |

---

## Test Results (2026-01-01)

**Total: 97 tests across 4 test suites, all passing**

| Test Suite | Tests | Command |
|------------|-------|---------|
| Basic Integration | 9/9 | `make integration-test` |
| Comprehensive (2x2-16x16) | 40/40 | `make comprehensive-test` |
| Latin Generator | 29/29 | `make verified-test` |
| JNI Interface | 19/19 | `make jni-test` |
| **All Tests** | **97/97** | `make all-tests` |

### Performance Results (2x2 to 16x16)

| Size | Matrix Rows | Matrix Cols | DLX Nodes | Time (ms) | Verified |
|------|-------------|-------------|-----------|-----------|----------|
| 2x2 | 8 | 12 | 24 | 0.02 | YES |
| 3x3 | 27 | 27 | 81 | 0.01 | YES |
| 4x4 | 64 | 48 | 192 | 0.04 | YES |
| 5x5 | 125 | 75 | 375 | 0.10 | YES |
| 6x6 | 216 | 108 | 648 | 0.26 | YES |
| 7x7 | 343 | 147 | 1029 | 0.61 | YES |
| 8x8 | 512 | 192 | 1536 | 1.31 | YES |
| 9x9 | 729 | 243 | 2187 | 2.56 | YES |
| 10x10 | 1000 | 300 | 3000 | 4.71 | YES |
| 11x11 | 1331 | 363 | 3993 | 8.20 | YES |
| 12x12 | 1728 | 432 | 5184 | 13.59 | YES |
| 13x13 | 2197 | 507 | 6591 | 22.48 | YES |
| 14x14 | 2744 | 588 | 8232 | 33.60 | YES |
| 15x15 | 3375 | 675 | 10125 | 53.98 | YES |
| 16x16 | 4096 | 768 | 12288 | 78.04 | YES |

**Scaling**: Approximately O(n^4) time complexity, viable for all supported sizes.

**Build command**: `cd formal && make all-tests`

---

## Next Steps

1. **Complete Coq Proofs**: Replace `Admitted` with actual proofs
2. ~~**Extract to OCaml**: Run `Extraction` to generate .ml files~~ DONE
3. ~~**Translate to C**: Manual or automated OCaml→C translation~~ DONE
4. ~~**Integrate DLX**: Create bridge module~~ DONE (dlx_latin_bridge.c)
5. ~~**Create Latin Generator Wrapper**: API-compatible interface~~ DONE (latin_verified.c)
6. ~~**Create JNI Interface**: Android-compatible API~~ DONE (keen_verified_jni.c)
7. ~~**Comprehensive Testing**: All grid sizes 2-16~~ DONE (97/97 tests)
8. **Wire to keen-android-jni.c**: Call kv_jni_generate_latin from JNI
9. **Add Z3 Backend**: Implement z3_cage_solver.c for cage constraints
10. **Android Integration**: Link verified library into APK build

---

## References

- Knuth, D. "Dancing Links" (arXiv:cs/0011047)
- de Moura & Bjørner, "Z3: An Efficient SMT Solver"
- Coq Reference Manual (v9.1)
- [HYBRID_DLX_SAT_ARCHITECTURE.md](./HYBRID_DLX_SAT_ARCHITECTURE.md)
- [LATIN_SQUARE_THEORY.md](./LATIN_SQUARE_THEORY.md)
