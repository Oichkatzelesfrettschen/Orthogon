# Static Analysis Report: KeenKenning Codebase

**Date:** 2025-01-01
**Tools Used:** cppcheck 2.x, lizard, coqchk (Rocq 9.1.0), Z3 4.15.5
**Scope:** Formal verification C code, JNI native code, Rocq proofs, SMT specifications

## Executive Summary

| Category | Status | Issues Found |
|----------|--------|--------------|
| Formal C Code | PASS | 2 style, 1 warning |
| JNI Native Code | NEEDS ATTENTION | 1 error, 15+ warnings |
| Cyclomatic Complexity | HIGH RISK | 3 functions CCN > 100 |
| Rocq Proofs | VERIFIED | All 5 modules pass coqchk |
| Z3 SMT Specs | VALID | Constraints satisfiable |

## 1. Static Analysis Results

### 1.1 Formal Verification C Code (`formal/*.c`)

**cppcheck Results:** Clean (minor style issues only)

| File | Issue | Severity | Description |
|------|-------|----------|-------------|
| dlx_latin_bridge.c:175 | constVariablePointer | style | `sol_rows` can be const |
| dlx_latin_bridge.c:244 | constVariablePointer | style | `sol_rows` can be const |
| test_latin_verified.c:46 | nullPointerOutOfMemory | warning | Missing malloc failure check |

**Unused Functions:**
- `kv_print_latin_stats` - Debug helper, expected unused
- `kv_add_cage_cnf` - Library function for external use
- `kv_write_dimacs` - Library function for external use

### 1.2 JNI Native Code (`app/src/main/jni/*.c`)

**CRITICAL ISSUE:**

| File | Line | Type | Description |
|------|------|------|-------------|
| tree234.c | 519 | ERROR | Array index out of bounds (`n->kids[4]` where array size is 4) |

**High-Priority Warnings:**

| File | Line | Type | Description |
|------|------|------|-------------|
| tree234.c | 1258 | nullPointerRedundantCheck | Potential null pointer dereference in `halves[half]` |
| tree234.c | 73-223 | nullPointerOutOfMemory | Multiple malloc failures not checked |

**Style Issues:**

| Category | Count | Files Affected |
|----------|-------|----------------|
| constParameterPointer | 12 | keen_generate.c, keen_solver.c, latin.c, random.c |
| unusedStructMember | 9 | keen.c (legacy struct fields) |
| variableScope | 6 | keen.c, keen_generate.c, latin.c, random.c |
| knownConditionTrueFalse | 4 | keen_generate.c (loop optimization patterns) |

### 1.3 Cyclomatic Complexity (lizard)

**CRITICAL - Functions exceeding CCN 15 threshold:**

| Function | File | CCN | NLOC | Risk |
|----------|------|-----|------|------|
| `new_game_desc` | keen_generate.c:403 | **182** | 466 | EXTREME |
| `new_game_desc_from_grid` | keen_generate.c:1200 | **165** | 433 | EXTREME |
| `solver_common` | keen_solver.c:147 | **120** | 273 | EXTREME |
| `maxflow_with_scratch` | maxflow_optimized.c:103 | 41 | 96 | HIGH |
| `latin_solver_set` | latin.c:174 | 40 | 107 | HIGH |
| `findtest` | tree234.c:1847 | 34 | 71 | HIGH |
| `check_cage_constraint` | keen_validate.c:154 | 34 | 83 | HIGH |
| `add234_insert` | tree234.c:121 | 33 | 195 | HIGH |

**Recommendation:** The `new_game_desc` and `solver_common` functions are monolithic and should be refactored into smaller, focused functions.

## 2. Formal Verification Status

### 2.1 Rocq Proof Verification (coqchk)

All proofs independently verified with Rocq 9.1.0:

| Module | Compilation | Independent Check | Theorems |
|--------|-------------|-------------------|----------|
| KeenKenning.Modes | PASS | VERIFIED | mode_flags_valid, classik_subset_kenning |
| KeenKenning.LatinSquare | PASS | VERIFIED | Row/column validity, uniqueness |
| KeenKenning.LatinEnum | PASS | VERIFIED | latin_3x3_count, constraint_expansion |
| KeenKenning.DLX | PASS | VERIFIED | Cover/uncover correctness |
| KeenKenning.SAT | PASS | VERIFIED | CNF clause generation |

**Compiler Warnings (informational):**
- `non-recursive` in DLX.v:166 - Fixpoint doesn't recurse (expected)
- `abstract-large-number` in LatinEnum.v - Large nat literals (expected)
- `native-compiler-disabled` - VM compute fallback (expected)

### 2.2 Z3 SMT Verification

| Specification | Result | Model |
|---------------|--------|-------|
| LatinSquare4x4.smt2 | SAT | Valid 4x4 Latin square found |
| LatinSquareSMT.smt2 | UNSAT | Constraint system verified |

**Note:** Z3 found a valid 4x4 Latin square solution:
```
4 3 1 2
3 2 4 1
2 1 3 4
1 4 2 3
```

## 3. Recommendations

### 3.1 Critical Fixes (Must Address)

1. **tree234.c:519 - Array bounds error**
   ```c
   // Current (BUGGY):
   if (n->kids[kcount])  // kcount can be 4, but array size is 4 (indices 0-3)

   // Fix: Add bounds check before loop exit
   for (kcount = 0; kcount < 4; kcount++) {
       // ... existing logic ...
   }
   if (kcount < 4 && n->kids[kcount])  // Guard against out-of-bounds
   ```

2. **tree234.c - Malloc failure handling**
   - Add null checks after all `snew()` calls
   - Or use wrapper that aborts on failure (acceptable for Android)

### 3.2 High Priority (Should Address)

1. **Refactor `new_game_desc` (CCN 182)**
   - Extract cage generation into separate function
   - Extract difficulty calibration into separate function
   - Target: CCN < 30 per function

2. **Refactor `solver_common` (CCN 120)**
   - Split constraint propagation phases
   - Extract branching logic
   - Target: CCN < 25 per function

### 3.3 Low Priority (Nice to Have)

1. Add `const` qualifiers to parameters (12 instances)
2. Remove unused struct members in `keen.c` (legacy from SGT Puzzles)
3. Reduce variable scope where flagged

## 4. Metrics Summary

### Code Statistics

| Category | Files | Lines | Functions |
|----------|-------|-------|-----------|
| Formal C | 8 | ~2,500 | 45 |
| JNI Native | 13 | ~15,000 | 180 |
| Rocq Proofs | 5 | ~2,100 | 85 theorems |
| SMT Specs | 2 | ~400 | 20 assertions |

### Proof Coverage

| Domain | Formalized | Verified |
|--------|------------|----------|
| Latin square properties | Yes | coqchk |
| DLX algorithm correctness | Yes | coqchk |
| SAT encoding soundness | Yes | coqchk |
| Mode flag constraints | Yes | coqchk |
| 4x4 satisfiability | Yes | Z3 |

## 5. Tool Configuration

### cppcheck
```bash
cppcheck --enable=all --std=c23 --suppress=missingIncludeSystem <files>
```

### lizard
```bash
lizard --CCN 15 --length 200 --warnings_only <files>
```

### coqchk
```bash
eval $(opam env --switch=rocq-isolated)
coqchk -Q . KeenKenning KeenKenning.<Module>
```

### Z3
```bash
z3 <spec>.smt2
```

## 6. Appendix: Full Tool Output

### cppcheck Formal Code
- 2 style issues (constVariablePointer)
- 1 warning (nullPointerOutOfMemory in test code)
- 3 unused functions (expected - library functions)

### cppcheck JNI Code
- 1 error (arrayIndexOutOfBounds)
- 15 warnings (nullPointerOutOfMemory, nullPointerRedundantCheck)
- 40+ style issues (constParameter, variableScope, etc.)

### lizard High-Complexity Functions
- 23 functions exceed CCN 15 threshold
- 3 functions exceed CCN 100 (critical)
- Average CCN across codebase: ~12

---

*Generated by KeenKenning formal verification toolchain audit*
