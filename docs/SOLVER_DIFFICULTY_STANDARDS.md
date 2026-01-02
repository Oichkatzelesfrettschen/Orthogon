# Solver Difficulty Standards

## Executive Summary

This document reconciles the difficulty grading infrastructure across the KeenKenning
solver algorithms, addressing the mathematical limitations of small grids and proposing
constraint expansion techniques to enable HARD+ difficulties for 2x2 and 3x3 puzzles.

## Current 7-Level Difficulty System

The solver uses a 7-level difficulty hierarchy mapped from `latin.c`:

| Level | Name | C Constant | Techniques Used |
|-------|------|------------|-----------------|
| 0 | Easy | `DIFF_EASY` | Single-candidate deductions only |
| 1 | Normal | `DIFF_NORMAL` | Pointing pairs, box/line reduction |
| 2 | Hard | `DIFF_HARD` | Naked/hidden sets, X-wing patterns |
| 3 | Extreme | `DIFF_EXTREME` | Forcing chains, region analysis |
| 4 | Unreasonable | `DIFF_UNREASONABLE` | Limited backtracking |
| 5 | Ludicrous | `DIFF_LUDICROUS` | Extensive trial-and-error |
| 6 | Incomprehensible | `DIFF_INCOMPREHENSIBLE` | Deep recursion, full backtracking |

### Key Implementation Details

From `keen_solver.c`:
- EASY/NORMAL/HARD use distinct Latin solver techniques
- EXTREME+ all call `solver_common(solver, vctx, DIFF_HARD)` with additional `latin.c` techniques
- The solver returns `diff_unfinished=12` when techniques are exhausted without solving

## Small Grid Mathematical Limitations

### Latin Square Counts by Size

| Grid Size | Total Latin Squares | Essentially Different | HARD+ Feasible |
|-----------|---------------------|----------------------|----------------|
| 2x2 | 2 | 1 | No (trivial) |
| 3x3 | 12 | 1 | Limited* |
| 4x4 | 576 | 4 | Yes |
| 5x5 | 161,280 | 56 | Yes |
| 6x6+ | Millions+ | Many | Yes |

*3x3 is limited because only 12 distinct squares exist, restricting cage configurations.

### Why 3x3 HARD+ Fails (Standard Mode)

1. **Small search space**: 12 Latin squares means most cage configurations have 1-2 solutions
2. **Technique exhaustion**: Advanced techniques (set exclusion, forcing chains) find nothing to operate on
3. **Solver behavior**: Returns `diff_unfinished=12` after exhausting all techniques

**Evidence**: Exhaustive testing showed 0% success rate for 3x3 HARD+ puzzles.

## Proposed Solutions: Constraint Expansion for Small Grids

### Approach 1: Automatic Mode Upgrade

When grid size = 3 and difficulty >= HARD, automatically enable constraint-expanding modes:

```
3x3 + HARD     -> KILLER + MYSTERY
3x3 + EXTREME  -> KILLER + BITWISE
3x3 + UNREASONABLE+ -> KILLER + BITWISE + MODULAR
```

### Approach 2: Explicit Mode Requirements

Require specific game modes for small grid high difficulties:

| Grid | Difficulty | Required Mode(s) |
|------|------------|------------------|
| 3x3 | HARD | KILLER or MYSTERY |
| 3x3 | EXTREME | KILLER + (MYSTERY or BITWISE) |
| 3x3 | UNREASONABLE+ | Not recommended |

### Approach 3: Meta-Puzzle System (Future)

Combine multiple small grids with shared constraints (like Samurai Sudoku):
- 4 overlapping 3x3 grids sharing corner cells
- Cross-grid cage constraints
- Enables complex deduction chains across grids

## Constraint Mode Effects on Difficulty

### KILLER Mode (`0x40`)

- Adds: No repeated digits within cages
- Effect: Reduces valid cage configurations, enables set-based deductions
- Small grid impact: **HIGH** - creates exclusion constraints in multi-cell cages

### MYSTERY Mode (`0x02`)

- Adds: Hidden operation symbols
- Effect: Forces deduction of operations from values
- Small grid impact: **MEDIUM** - adds deduction step but doesn't change search space

### BITWISE Mode (`0x800`)

- Adds: XOR operations
- Effect: Very high ambiguity (many digit combinations produce same XOR result)
- Small grid impact: **HIGH** - XOR ambiguity creates complex deduction scenarios

### MODULAR Mode (`0x20`)

- Adds: Wrap-around arithmetic (mod N)
- Effect: Changes how clue values are interpreted
- Small grid impact: **MEDIUM** - enables unusual cage configurations

## Implementation Recommendations

### Phase 1: UI Constraint (SUPERSEDED)

~~Limit 3x3 to EASY/NORMAL in standard mode (implemented in `Difficulty.forGridSize()`).~~

**Status:** SUPERSEDED by Phase 2. UI now allows all difficulties for all grid sizes.

### Phase 2: Automatic Mode Upgrade (IMPLEMENTED 2026-01-01)

Implemented in `keen_generate.c` lines 431-443 and 1214-1226:

```c
// Auto-upgrade 3x3 HARD+ to enable constraint modes
int mode_flags = params->mode_flags;
if (w == 3 && diff >= DIFF_HARD) {
    mode_flags |= MODE_KILLER;
    if (diff >= DIFF_EXTREME) {
        mode_flags |= MODE_BITWISE;
    }
    if (diff >= DIFF_UNREASONABLE) {
        mode_flags |= MODE_MODULAR;
    }
}
```

**UI Update:** `Difficulty.forGridSize()` now returns all difficulties for all sizes.

### Phase 3: Hybrid Solver Integration

Use DLX+SAT architecture (see `docs/HYBRID_DLX_SAT_ARCHITECTURE.md`) to handle
complex constraint combinations more efficiently.

## Difficulty Calibration Guidelines

### Generating Puzzles

1. Start with target difficulty level
2. Generate cage configuration
3. Attempt solve at target difficulty
4. If solver returns `diff_unfinished`:
   - Regenerate cages (different configuration)
   - Or downgrade difficulty
   - Or (for small grids) enable constraint-expanding mode

### Validating Difficulty

```
Actual Difficulty = min(target_diff, solver_achieved_diff)
```

If actual < target consistently (>50% of attempts), the grid size/mode combination
cannot support the target difficulty.

## Cross-Module Reconciliation

### Files Affected

| File | Role | Difficulty Handling |
|------|------|-------------------|
| `keen_solver.c` | Cage constraint solving | 7-level mapping via usersolver callbacks |
| `latin.c` | Core Latin square solving | `diff_simple`, `diff_set_*`, `diff_forcing`, `diff_recursive` |
| `keen_generate.c` | Puzzle generation | Validates difficulty achievability |
| `GameMode.kt` | Android enum | `Difficulty.forGridSize()` filters |
| `MenuScreen.kt` | UI | Uses filtered difficulty list |

### Consistency Checks

1. Native layer difficulty constants must match Kotlin `Difficulty.level` values
2. Mode flags must be consistent between `keen_modes.h` and `GameMode.cFlags`
3. Solver timeout handling must be uniform across difficulty levels

## References

- [Latin square constraint satisfaction](https://mienxiu.com/solving-latin-squares-as-csps/)
- [KenKen solver implementations](https://github.com/chanioxaris/kenken-solver)
- [Puzzle difficulty metrics](https://github.com/ghfbsd/kenken-maker)
- [Hybrid DLX+SAT Architecture](./HYBRID_DLX_SAT_ARCHITECTURE.md)
- [Latin Square Wikipedia](https://en.wikipedia.org/wiki/Latin_square)

## Appendix: 2x2 Grid Analysis

2x2 grids have only 2 possible Latin squares:
```
1 2    2 1
2 1    1 2
```

These are trivially solvable and cannot support any difficulty level beyond EASY.
**Recommendation**: Do not support 2x2 grids, or use meta-puzzle approach only.

## Appendix: Cross-Module Verification (2025-01-01)

### Difficulty Level Alignment

| Kotlin Enum | Kotlin Level | C Constant | C Value | Status |
|-------------|--------------|------------|---------|--------|
| `EASY` | 0 | `DIFF_EASY` | 0 | ALIGNED |
| `NORMAL` | 1 | `DIFF_NORMAL` | 1 | ALIGNED |
| `HARD` | 2 | `DIFF_HARD` | 2 | ALIGNED |
| `EXTREME` | 3 | `DIFF_EXTREME` | 3 | ALIGNED |
| `UNREASONABLE` | 4 | `DIFF_UNREASONABLE` | 4 | ALIGNED |
| `LUDICROUS` | 5 | `DIFF_LUDICROUS` | 5 | ALIGNED |
| `INCOMPREHENSIBLE` | 6 | `DIFF_INCOMPREHENSIBLE` | 6 | ALIGNED |

### Mode Flag Alignment

| Kotlin GameMode | Kotlin cFlags | C Constant | C Value | Status |
|-----------------|---------------|------------|---------|--------|
| `STANDARD` | 0x00 | `MODE_STANDARD` | 0x0000 | ALIGNED |
| `MULTIPLICATION_ONLY` | 0x01 | `MODE_MULT_ONLY` | 0x0001 | ALIGNED |
| `MYSTERY` | 0x02 | `MODE_MYSTERY` | 0x0002 | ALIGNED |
| `ZERO_INCLUSIVE` | 0x04 | `MODE_ZERO_INCLUSIVE` | 0x0004 | ALIGNED |
| `NEGATIVE_NUMBERS` | 0x08 | `MODE_NEGATIVE` | 0x0008 | ALIGNED |
| `EXPONENT` | 0x10 | `MODE_EXPONENT` | 0x0010 | ALIGNED |
| `MODULAR` | 0x20 | `MODE_MODULAR` | 0x0020 | ALIGNED |
| `KILLER` | 0x40 | `MODE_KILLER` | 0x0040 | ALIGNED |
| `HINT_MODE` | 0x80 | `MODE_HINT` | 0x0080 | ALIGNED |
| `ADAPTIVE` | 0x100 | `MODE_ADAPTIVE` | 0x0100 | ALIGNED |
| `STORY` | 0x200 | `MODE_STORY` | 0x0200 | ALIGNED |
| `RETRO_8BIT` | 0x0000 | N/A (UI-only) | N/A | UI-ONLY |
| `BITWISE` | 0x800 | `MODE_BITWISE` | 0x0800 | ALIGNED |

### Issues Found and Resolved

1. **RETRO_8BIT Flag Collision (FIXED 2025-01-01)**
   - Issue: `RETRO_8BIT` had `cFlags = 0x400` which collided with `MODE_NUMBER_THEORY`
   - Resolution: Changed to `cFlags = 0x0000` since it's a UI-only visual theme
   - Rationale: RETRO_8BIT only affects rendering, not puzzle generation

### Special Return Codes (latin.h)

| Name | Value | Meaning |
|------|-------|---------|
| `diff_impossible` | 10 | No valid solution exists |
| `diff_ambiguous` | 11 | Multiple solutions exist |
| `diff_unfinished` | 12 | Techniques exhausted, puzzle not solvable at target difficulty |

### Verification Script

To verify alignment during builds, ensure:
```sh
# Count difficulty levels match
grep -c "DIFF_" keen_internal.h  # Should match Difficulty.entries.size
# Count mode flags match
grep -c "MODE_" keen_modes.h     # Should be >= GameMode.entries.size
```
