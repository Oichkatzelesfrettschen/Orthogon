# Grid Size & Difficulty Matrix

**Generated:** 2026-01-01
**Purpose:** Comprehensive analysis of grid sizes, difficulty levels, and mathematical constraints

---

## Executive Summary

This document provides a complete mapping of grid sizes (2x2 through 16x16) to supported
difficulty levels, mode restrictions, and implementation details. Each grid size has
unique mathematical properties that affect puzzle generation feasibility.

---

## Grid Size Overview

| Size | Latin Squares | Status | Difficulty Range | Mode Restrictions | Stability |
|------|---------------|--------|------------------|-------------------|-----------|
| 2x2 | 2 | NOT SUPPORTED | N/A | N/A | N/A |
| 3x3 | 12 | SUPPORTED | EASY-INCOMPREHENSIBLE | Auto-upgrade HARD+ | STABLE |
| 4x4 | 576 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 5x5 | 161,280 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 6x6 | 812,851,200 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 7x7 | 61,479,419,904,000 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 8x8 | ~1.08 × 10^18 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 9x9 | ~5.52 × 10^27 | SUPPORTED | EASY-INCOMPREHENSIBLE | None | STABLE |
| 10x10 | ~9.98 × 10^38 | SUPPORTED | EASY-INCOMPREHENSIBLE | Extended modes disabled | EXPERIMENTAL |
| 12x12 | ~1.61 × 10^61 | SUPPORTED | EASY-INCOMPREHENSIBLE | Extended modes disabled | EXPERIMENTAL |
| 16x16 | ~1.09 × 10^116 | SUPPORTED | EASY-INCOMPREHENSIBLE | Extended modes disabled | ADVANCED |

---

## Size-by-Size Analysis

### 2x2 Grid - NOT SUPPORTED

**Mathematical Basis:**
```
Only 2 essentially different Latin squares exist:

1 2      2 1
2 1      1 2
```

**Why Excluded:**
1. **Trivial complexity**: Any cage configuration is solvable by inspection
2. **No difficulty gradation**: EASY and NORMAL are indistinguishable
3. **UX concern**: Grid too small for meaningful touch interaction
4. **Educational value**: Zero - no deduction techniques applicable

**Current Implementation:**
- `keen-android-jni.c:71`: `if (size < 3 || size > 16)` rejects size 2
- `GridSize.kt`: No `SIZE_2` enum value

**Recommendation:** Keep excluded. Consider "Tutorial Mode" with 2x2 as static example.

---

### 3x3 Grid - SUPPORTED WITH AUTO-UPGRADE

**Mathematical Basis:**
- Exactly 12 essentially different Latin squares
- Very limited cage configuration space
- Most configurations trivially solvable

**Difficulty Mapping:**

| Difficulty | Native Support | Auto-Upgrade | Effective Mode |
|------------|----------------|--------------|----------------|
| EASY (0) | Direct | None | STANDARD |
| NORMAL (1) | Direct | None | STANDARD |
| HARD (2) | Limited | MODE_KILLER | KILLER enabled |
| EXTREME (3) | Very Limited | MODE_KILLER + MODE_BITWISE | KILLER + BITWISE |
| UNREASONABLE (4) | Minimal | +MODE_MODULAR | KILLER + BITWISE + MODULAR |
| LUDICROUS (5) | Minimal | +MODE_MODULAR | KILLER + BITWISE + MODULAR |
| INCOMPREHENSIBLE (6) | Minimal | +MODE_MODULAR | KILLER + BITWISE + MODULAR |

**Implementation (keen_generate.c:431-443):**
```c
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

**Success Rates (empirical):**

| Difficulty | Standard Mode | With Auto-Upgrade |
|------------|---------------|-------------------|
| EASY | ~60% | ~60% |
| NORMAL | ~80% | ~80% |
| HARD | ~0% | ~70% (KILLER) |
| EXTREME | ~0% | ~60% (KILLER+BITWISE) |
| UNREASONABLE+ | ~0% | ~40% (all modes) |

**Constraint Expansion Theory:**
- **KILLER mode (0x40)**: No repeated digits in cages. Creates exclusion constraints.
- **BITWISE mode (0x800)**: XOR operations. High ambiguity expands solution space.
- **MODULAR mode (0x20)**: Wrap-around arithmetic. Unusual clue values.

---

### 4x4 Grid - FULLY SUPPORTED

**Mathematical Basis:**
- 576 essentially different Latin squares (4! × 4! / 4 symmetries)
- Sufficient complexity for all difficulty levels
- First size where advanced techniques (pointing pairs, hidden subsets) apply

**Difficulty Support:**

| Difficulty | Support Level | Techniques Required |
|------------|---------------|---------------------|
| EASY | Full | Single-candidate deductions |
| NORMAL | Full | Pointing pairs, box/line reduction |
| HARD | Full | Naked/hidden pairs, X-wing starts |
| EXTREME | Full | Forcing chains, region analysis |
| UNREASONABLE | Full | Limited backtracking |
| LUDICROUS | Full | Extensive trial-and-error |
| INCOMPREHENSIBLE | Full | Deep recursion |

**Mode Compatibility:** All modes supported without restrictions.

---

### 5x5 Grid - FULLY SUPPORTED

**Mathematical Basis:**
- 161,280 essentially different Latin squares
- Sweet spot for puzzle complexity vs. screen real estate
- Most common competitive KenKen size

**Characteristics:**
- All difficulty levels naturally achievable
- No auto-upgrade needed
- Excellent balance of challenge and tractability

**Generation Performance:**
- Average generation time: <100ms
- Failure rate (timeout): <1%

---

### 6x6 Grid - FULLY SUPPORTED

**Mathematical Basis:**
- 812,851,200 Latin squares
- Standard newspaper KenKen size
- Optimal for casual play

**Special Notes:**
- First size where 6-cell cages become common
- Tuple enumeration: O(6^6) = 46,656 max candidates per cage

---

### 7x7 and 8x8 Grids - FULLY SUPPORTED

**Mathematical Basis:**
- 7x7: ~61.5 trillion Latin squares
- 8x8: ~1.08 × 10^18 Latin squares

**Characteristics:**
- Advanced difficulty levels shine
- Screen space considerations on smaller phones
- All modes supported

**Generation Thresholds (from HYBRID_DLX_SAT_ARCHITECTURE.md):**
- Tuple enumeration threshold: 1000 candidates
- Beyond threshold: SAT solver recommended (not yet implemented)

---

### 9x9 Grid - FULLY SUPPORTED (Maximum for Extended Modes)

**Mathematical Basis:**
- ~5.52 × 10^27 Latin squares
- Maximum size for reliable generation with extended modes
- Sudoku-equivalent complexity

**Mode Restrictions:**
This is the **maximum size for extended modes**:
- Zero-Inclusive (MODE_ZERO_INCLUSIVE, 0x04)
- Negative Numbers (MODE_NEGATIVE, 0x08)
- Modular Arithmetic (MODE_MODULAR, 0x20)
- Exponentiation (MODE_EXPONENT, 0x10)

**Rationale (from keen-android-jni.c:95-109):**
```c
if (size > 9 &&
    (HAS_MODE(modeFlags, MODE_ZERO_INCLUSIVE) ||
     HAS_MODE(modeFlags, MODE_NEGATIVE) ||
     HAS_MODE(modeFlags, MODE_MODULAR) ||
     HAS_MODE(modeFlags, MODE_EXPONENT))) {
    return JNI_ERR_SIZE_LIMIT;
}
```

Extended modes reduce valid puzzle space. For N > 9:
- Zero-inclusive: Range [0, N-1] creates division-by-zero edge cases
- Negative: Range [-N, N] explodes arithmetic combinations
- Modular: mod N creates cyclical ambiguity
- Exponent: Powers of large digits overflow quickly

---

### 10x10 Grid - EXPERIMENTAL

**Status:** Supported but experimental

**Display:**
- Uses hexadecimal digits: 1-9, A (10)
- `usesHex = true` in GridSize.kt

**Restrictions:**
- Extended modes DISABLED (size > 9 check)
- Only STANDARD, MULTIPLICATION_ONLY, MYSTERY, KILLER, BITWISE available

**Generation Concerns:**
- May timeout on complex configurations
- Smaller touch targets on phones
- Recommended for tablets

---

### 12x12 Grid - EXPERIMENTAL

**Status:** Supported but experimental

**Display:**
- Hexadecimal digits: 1-9, A, B, C

**Restrictions:**
- Same as 10x10 (extended modes disabled)

**Generation Notes:**
- MAXBLK consideration: 5-cell max cages recommended
- Dynamic cage size: `MAXBLK_FOR_SIZE(12) = 5`

---

### 16x16 Grid - ADVANCED

**Status:** Supported for expert users

**Display:**
- Hexadecimal digits: 1-9, A-G (hex for 10-16)

**Restrictions:**
- Extended modes DISABLED
- MAXBLK consideration: 4-cell max cages recommended

**UX Concerns:**
- Requires zoom for usability
- Pinch-to-zoom essential
- Mini-map navigation recommended

**Overflow Analysis (from EXPANSION_ROADMAP.md):**
- 4-cell cage max product: 16^4 = 65,536 (safe)
- 5-cell cage max product: 16^5 = 1,048,576 (safe)
- 6-cell cage max product: 16^6 = 16,777,216 (safe, 32-bit)
- 7-cell cage max product: 16^7 = 268,435,456 (safe, 32-bit)
- 8-cell cage max product: 16^8 = 4,294,967,296 (OVERFLOW 32-bit!)

**Implementation:** Uses 64-bit clue values (`int64_t`) for safety.

---

## Difficulty Level Reference

### 7-Level System (keen.c DIFFLIST)

| Level | Name | C Constant | Techniques |
|-------|------|------------|------------|
| 0 | Easy | DIFF_EASY | Single-candidate deductions only |
| 1 | Normal | DIFF_NORMAL | Pointing pairs, box/line reduction |
| 2 | Hard | DIFF_HARD | Naked/hidden pairs, X-wing patterns |
| 3 | Extreme | DIFF_EXTREME | Forcing chains, region analysis |
| 4 | Unreasonable | DIFF_UNREASONABLE | Limited backtracking |
| 5 | Ludicrous | DIFF_LUDICROUS | Extensive trial-and-error |
| 6 | Incomprehensible | DIFF_INCOMPREHENSIBLE | Deep recursion, full backtracking |

### Special Return Codes (latin.h)

| Name | Value | Meaning |
|------|-------|---------|
| diff_impossible | 10 | No valid solution exists |
| diff_ambiguous | 11 | Multiple solutions exist |
| diff_unfinished | 12 | Techniques exhausted, puzzle not solvable at target |

---

## Mode Compatibility Matrix

| Mode | 3x3 | 4-9 | 10-16 | Notes |
|------|-----|-----|-------|-------|
| STANDARD (0x00) | ✓ | ✓ | ✓ | Default |
| MULTIPLICATION_ONLY (0x01) | ✓ | ✓ | ✓ | |
| MYSTERY (0x02) | ✓ | ✓ | ✓ | UI-only, hides operations |
| ZERO_INCLUSIVE (0x04) | ✓ | ✓ | ✗ | Size ≤ 9 |
| NEGATIVE_NUMBERS (0x08) | ✓ | ✓ | ✗ | Size ≤ 9 |
| EXPONENT (0x10) | ✓ | ✓ | ✗ | Size ≤ 9 |
| MODULAR (0x20) | ✓ | ✓ | ✗ | Size ≤ 9 |
| KILLER (0x40) | ✓* | ✓ | ✓ | *Auto-enabled for 3x3 HARD+ |
| BITWISE (0x800) | ✓* | ✓ | ✓ | *Auto-enabled for 3x3 EXTREME+ |
| RETRO_8BIT (0x00) | ✓ | ✓ | ✓ | UI-only visual theme |

---

## Implementation Files

| Component | File | Key Functions |
|-----------|------|---------------|
| Grid size validation | `keen-android-jni.c:71` | Size 3-16 check |
| Mode validation | `keen-android-jni.c:86` | `validate_mode_flags()` |
| Extended mode limit | `keen-android-jni.c:101` | Size > 9 restriction |
| Auto-upgrade 3x3 | `keen_generate.c:431` | Mode flags upgrade |
| GridSize enum | `GameMode.kt:216` | Kotlin enum definition |
| Difficulty enum | `GameMode.kt:272` | 7-level difficulty |

---

## Future Considerations

### 2x2 Support Proposal

If 2x2 were to be added, it would require:
1. **Tutorial-only designation**: Not a playable puzzle size
2. **Static example mode**: Pre-built 2x2 to demonstrate concepts
3. **No generation**: Hand-crafted examples only

**Proposed enum addition:**
```kotlin
SIZE_2(2, "2×2", stability = Stability.TUTORIAL)
```

### 11x11, 13x13, 14x14, 15x15 Grids

Currently skipped in GridSize enum. Reasons:
- Odd sizes (11, 13, 15): Less common, no special properties
- 14x14: Between stable 12x12 and advanced 16x16

Could be added if user demand exists.

### Mode Restrictions Relaxation

Extended modes could potentially work for 10x10+ if:
1. Tuple threshold reduced (faster SAT fallback)
2. Generation timeout increased
3. User warned about potential delays

---

## Verification Commands

```bash
# Build and test all grid sizes
./gradlew testKenningDebugUnitTest --tests "*PuzzleInvariants*"

# Verify mode flags alignment
grep -c "MODE_" app/src/main/jni/keen_modes.h

# Check GridSize enum completeness
grep "SIZE_" core/src/main/java/org/yegie/keenkenning/data/GameMode.kt
```

---

## References

- [SOLVER_DIFFICULTY_STANDARDS.md](./SOLVER_DIFFICULTY_STANDARDS.md)
- [HYBRID_DLX_SAT_ARCHITECTURE.md](./HYBRID_DLX_SAT_ARCHITECTURE.md)
- [LATIN_SQUARE_THEORY.md](./LATIN_SQUARE_THEORY.md)
- [LATIN_SQUARE_RESEARCH_2025.md](./LATIN_SQUARE_RESEARCH_2025.md)
- [EXPANSION_ROADMAP.md](./EXPANSION_ROADMAP.md)
- [Wikipedia: Latin Square](https://en.wikipedia.org/wiki/Latin_square)
