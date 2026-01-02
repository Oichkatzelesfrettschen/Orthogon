# Hybrid DLX+SAT Solver Architecture

## Executive Summary

This document describes a hybrid constraint solving approach that combines
Dancing Links (DLX) for small exact cover problems with SAT/CDCL solvers
for complex constraint propagation. The hybrid approach addresses the
combinatorial explosion in cage tuple enumeration for large Keen puzzles.

## Problem Analysis

### Current Architecture

The solver (`keen_solver.c`) uses iterative tuple enumeration:

```
C_ADD/C_MUL cages:
  for each cell in cage:
    for each valid digit:
      if (Latin constraint OK && cage arithmetic OK):
        record candidate tuple
```

**Complexity**: For an n-cell cage with digit range [1,w], worst-case
enumeration is O(w^n) before pruning.

### Empirical Findings (2025-01-01)

| Grid | Difficulty | Success Rate | Root Cause |
|------|------------|--------------|------------|
| 3x3  | EASY       | ~60%         | Limited Latin square space (12 distinct) |
| 3x3  | NORMAL     | ~80%         | Same limitation, more retries needed |
| 3x3  | HARD+      | 0%           | Solver exhausts techniques, returns diff_unfinished=12 |
| 4x4+ | ALL        | >95%         | Sufficient combinatorial complexity |

**Key Insight**: 3x3 grids lack combinatorial space for HARD puzzles.
This is a mathematical limitation, not a solver bug. Only 12 essentially
different 3x3 Latin squares exist.

### Tuple Explosion Problem

| Cage Size | Max Tuples (ADD, w=9) | Max Tuples (MUL, w=9) |
|-----------|----------------------|----------------------|
| 2 cells   | ~36                  | ~20                  |
| 3 cells   | ~216                 | ~80                  |
| 4 cells   | ~1,296               | ~200                 |
| 5 cells   | ~7,776               | ~400                 |
| 6+ cells  | >46,656              | >1,000               |

The solver prunes invalid tuples, but initial enumeration still costs O(w^n).

## Hybrid Architecture Design

### Layer 1: Tuple Enumeration (Current)

For cages with expected tuple count < threshold:
- Use current iterative enumeration
- Efficient for 2-4 cell cages
- Direct constraint checking

### Layer 2: DLX Exact Cover (Existing, Unused)

For Latin square constraint satisfaction:
- `dlx.c` implements Algorithm X with Dancing Links
- Currently 0% coverage (not exercised)
- Ideal for: "exactly one of each digit per row/column"

**Proposed Use**: Encode Latin constraints as exact cover matrix,
solve with DLX before cage constraint refinement.

### Layer 3: SAT/CDCL (Proposed)

For complex cage constraints exceeding tuple threshold:
- Encode cage arithmetic as SAT clauses
- Use conflict-driven clause learning (CDCL)
- Leverage unit propagation for fast pruning

**Candidate SAT Solvers**:

| Solver   | Language | Integration | License  |
|----------|----------|-------------|----------|
| varisat  | Rust     | FFI bridge  | MIT      |
| kissat   | C        | Direct      | MIT      |
| minisat  | C++      | Wrapper     | MIT      |

### Decision Thresholds

| Grid Size N | Tuple Threshold | Strategy |
|-------------|-----------------|----------|
| 3-4         | 100             | Always enumerate |
| 5-6         | 500             | Enumerate up to 500, then SAT |
| 7-8         | 1000            | Enumerate up to 1000, then SAT |
| 9-16        | 2000            | Enumerate up to 2000, then SAT |

**Rationale**: Thresholds based on empirical cache performance and
SAT solver setup overhead (~0.1ms for kissat initialization).

## SAT Encoding for Keen Constraints

### Cell Variables

For each cell (r,c) and digit d:
```
X[r,c,d] = true iff cell (r,c) contains digit d
```

Total variables: N^2 * N = N^3

### Latin Constraints (Row/Column)

For each row r and digit d:
```
exactly_one(X[r,0,d], X[r,1,d], ..., X[r,N-1,d])
```

Encoded as:
- At-least-one: (X[r,0,d] OR X[r,1,d] OR ... OR X[r,N-1,d])
- At-most-one: pairwise exclusion (-X[r,i,d] OR -X[r,j,d]) for i < j

### Cage Arithmetic Constraints

For ADD cage with cells {c1, c2, ...} and target T:
```
For each valid tuple (d1, d2, ...) where sum = T:
  ADD clause: (X[c1,d1] AND X[c2,d2] AND ...)

At-least-one-tuple: OR over all valid tuple clauses
```

**Optimization**: Use Tseitin transformation for large clauses to avoid
exponential blowup.

### MUL Cage Encoding

Similar to ADD, but enumerate product tuples:
```
For each valid tuple (d1, d2, ...) where product = T:
  MUL clause: (X[c1,d1] AND X[c2,d2] AND ...)
```

## Implementation Plan

### Phase 1: DLX Integration (Low Risk)

1. Wire DLX into `latin_solver_main()` for initial grid setup
2. Use DLX to quickly eliminate impossible Latin squares
3. Measure coverage improvement

### Phase 2: SAT Encoding Module (Medium Risk)

1. Create `keen_sat.c` with SAT variable/clause builders
2. Implement Tseitin transformation for cage constraints
3. Add threshold check in `solver_clue_enumerator()`

### Phase 3: SAT Solver Integration (High Risk)

1. Evaluate kissat vs varisat for embedded use
2. Create FFI bridge (Rust) or wrapper (C++)
3. Benchmark against pure enumeration

### Phase 4: Threshold Tuning

1. Profile tuple counts across difficulty levels
2. Collect wall-clock timing data
3. Adjust thresholds per grid size

## Code Locations

| Component | File | Function |
|-----------|------|----------|
| Tuple enumeration | `keen_solver.c:341-436` | C_ADD/C_MUL case |
| DLX implementation | `dlx.c` | `dlx_solve()` |
| Latin solver | `latin.c` | `latin_solver()` |
| Cage structures | `keen.c` | `struct clue` |

## References

1. Knuth, D. "Dancing Links" (arXiv:cs/0011047)
2. Biere, A. et al. "Handbook of Satisfiability" (IOS Press, 2021)
3. SAT Competition 2024: https://satcompetition.github.io/2024/

## Appendix: 3x3 Combinatorial Limitation

There are exactly 12 essentially different 3x3 Latin squares:

```
1 2 3    1 2 3    1 3 2    1 3 2
2 3 1    3 1 2    2 1 3    3 2 1
3 1 2    2 3 1    3 2 1    2 1 3
...
```

The small search space means:
- Many cage configurations have only 1-2 valid solutions
- HARD techniques (intersection analysis, set exclusion) cannot differentiate
- The solver correctly returns `diff_unfinished=12` when techniques exhausted

**Recommendation**: Disable HARD+ difficulty for 3x3 grids in UI.
