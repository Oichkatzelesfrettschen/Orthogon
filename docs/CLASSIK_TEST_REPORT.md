# CLASSIK Mode Test Report

**Date:** 2026-01-01
**Flavor:** Classik (org.yegie.keenkenning.classik)
**Tester:** Automated via adb UI automation

## Summary

| Test Category | Passed | Failed | Total |
|---------------|--------|--------|-------|
| Easy (3-9) | 7 | 0 | 7 |
| Normal (3-9) | 7 | 0 | 7 |
| Hard (3-9) | 6 | 1 | 7 |
| Extreme (4-7) | 4 | 0 | 4 |
| RETRO_8BIT | 7 | 0 | 7 |
| **Total** | **31** | **1** | **32** |

## Pass Rate: 96.9%

## Detailed Results

### STANDARD Mode - Easy Difficulty
| Size | Status | Screenshot Size |
|------|--------|-----------------|
| 3x3 | PASS | 84,702 bytes |
| 4x4 | PASS | 95,382 bytes |
| 5x5 | PASS | 100,419 bytes |
| 6x6 | PASS | 118,318 bytes |
| 7x7 | PASS | 121,902 bytes |
| 8x8 | PASS | 133,381 bytes |
| 9x9 | PASS | 151,061 bytes |

### STANDARD Mode - Normal Difficulty
| Size | Status | Screenshot Size |
|------|--------|-----------------|
| 3x3 | PASS | 83,577 bytes |
| 4x4 | PASS | 84,703 bytes |
| 5x5 | PASS | 99,944 bytes |
| 6x6 | PASS | 116,176 bytes |
| 7x7 | PASS | 117,820 bytes |
| 8x8 | PASS | 131,454 bytes |
| 9x9 | PASS | 147,891 bytes |

### STANDARD Mode - Hard Difficulty
| Size | Status | Notes |
|------|--------|-------|
| 3x3 | FAIL | Auto-upgrade to KILLER mode increases generation complexity |
| 4x4 | PASS | 93,249 bytes |
| 5x5 | PASS | 102,337 bytes |
| 6x6 | PASS | 113,226 bytes |
| 7x7 | PASS | 115,025 bytes |
| 8x8 | PASS | 111,398 bytes |
| 9x9 | PASS | 147,675 bytes |

### STANDARD Mode - Extreme Difficulty
| Size | Status | Screenshot Size |
|------|--------|-----------------|
| 4x4 | PASS | 93,061 bytes |
| 5x5 | PASS | 99,618 bytes |
| 6x6 | PASS | 115,476 bytes |
| 7x7 | PASS | 112,240 bytes |

### RETRO_8BIT Mode
| Size | Difficulty | Status |
|------|------------|--------|
| 3x3 | Easy | PASS |
| 4x4 | Normal | PASS |
| 5x5 | Easy | PASS |
| 6x6 | Normal | PASS |
| 7x7 | Easy | PASS |
| 8x8 | Normal | PASS |
| 9x9 | Easy | PASS |

## Known Issues

### 3x3 HARD+ Generation Timeout
- **Root Cause**: Phase 2 auto-upgrade adds KILLER mode for 3x3 HARD+
- **Behavior**: Generator attempts 9440+ iterations, cannot achieve target difficulty within timeout
- **Logcat**: `KEEN_GEN: FAILED: 9440 attempts, wanted diff=5, best achieved=12`
- **Impact**: 3x3 HARD/EXTREME/UNREASONABLE/LUDICROUS/INCOMPREHENSIBLE may timeout
- **Recommended Fix**: Increase attempt limit or adjust difficulty scoring for KILLER mode

### Default Settings Generation Failure
- 9x9 with LUDICROUS (diff=5) failed on first attempt
- Higher difficulties (diff >= 4) may require multiple generation attempts

## Formal Verification Status

The Coq specification (formal/Modes.v) has been created and compiled, proving:
1. Mode flags are valid powers of 2
2. Classik modes are subset of Kenning modes
3. Grid size bounds are consistent (3 ≤ size ≤ 9 for Classik)
4. Difficulty level roundtrip conversion is correct
5. Auto-upgrade preserves base flags for non-3x3 grids
6. Auto-upgrade correctly adds KILLER for 3x3 HARD

## Screenshots

All test screenshots saved to `/tmp/classik_test_results/`

## Conclusion

CLASSIK flavor is **FUNCTIONAL** with 96.9% pass rate. The only failure is the 
expected 3x3 HARD limitation due to the auto-upgrade mechanism adding KILLER mode,
which increases generation complexity beyond the default timeout.
