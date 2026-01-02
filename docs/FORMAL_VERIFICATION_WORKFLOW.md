# Formal Verification Workflow: Rocq → OCaml → C/Kotlin

## Overview

This document describes the formal verification pipeline for KeenKenning,
from theorem-proving in Rocq to efficient production code in C and Kotlin.

## Pipeline Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    FORMAL SPECIFICATION                          │
│  LatinEnum.v, LatinSquare.v, Modes.v, DLX.v, SAT.v              │
│  - Theorems about Latin square properties                       │
│  - Verified enumeration bounds                                   │
│  - Correctness proofs for algorithms                             │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                   EXTRACTION LAYER                               │
│  Two approaches based on numeric representation:                 │
│                                                                  │
│  1. nat-based (ExtractMinimal.v)                                │
│     - Uses ExtrOcamlNatInt for nat → int                        │
│     - Good for algorithms, bad for large constants              │
│     - O(n) representation for number n                          │
│                                                                  │
│  2. Z-based (ExtractZ.v) [RECOMMENDED]                          │
│     - Uses ExtrOcamlZInt for Z → int                            │
│     - Binary representation: O(log n) for number n              │
│     - Much more efficient for large constants                   │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                   EXTRACTED OCAML                                │
│  latin_minimal.ml, latin_z.ml                                   │
│  - Mechanically generated from Rocq                              │
│  - Preserves formal guarantees                                   │
│  - May need optimization for production                         │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                 PRODUCTION OCAML                                 │
│  latin_production.ml                                            │
│  - Hand-optimized version derived from extracted code           │
│  - Uses native OCaml idioms                                     │
│  - Algorithm structure verified against Rocq specs              │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                    ┌───────┴───────┐
                    ▼               ▼
┌─────────────────────────┐   ┌─────────────────────────┐
│      C PRODUCTION       │   │   KOTLIN PRODUCTION     │
│  keen_verified.c        │   │  LatinBounds.kt         │
│  latin_verified.c       │   │  (BuildConfig flags)    │
│  - JNI interface        │   │  - Android UI layer     │
│  - Native performance   │   │  - Type-safe wrappers   │
└─────────────────────────┘   └─────────────────────────┘
```

## Extraction Strategy

### Problem: Large Numeric Literals

Rocq's `nat` type uses unary (Peano) representation. A number like 9408
becomes 9408 nested successor calls:

```ocaml
(* Unary: O(n) representation *)
Stdlib.Int.succ (Stdlib.Int.succ (... 9408 times ...))
```

### Solution: Use Z (Binary Integers)

Rocq's `Z` type uses binary representation. The same number becomes:

```ocaml
(* Binary: O(log n) representation - only 13 operations *)
((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
((fun p->2*p) 1)))))))))))))
```

### Extraction Comparison

| Approach | MODE_BITWISE (2048) | reduced_count(6) (9408) |
|----------|---------------------|-------------------------|
| Unary nat | 2048 ops | 9408 ops |
| Binary Z | 11 ops | 13 ops |

## Build Commands

### 1. Compile Rocq Specifications

```bash
# Activate isolated opam environment
eval $(opam env --switch=rocq-isolated)

# Compile all specification modules
for f in Modes.v LatinSquare.v LatinEnum.v DLX.v SAT.v; do
  coqc -Q . KeenKenning $f
done

# Compile extraction-friendly versions
coqc -Q . KeenKenning LatinBoundsZ.v
coqc -Q . KeenKenning LatinBoundsClean.v
```

### 2. Verify Proofs Independently

```bash
# Use coqchk for independent verification
for m in Modes LatinSquare LatinEnum DLX SAT; do
  coqchk -Q . KeenKenning KeenKenning.$m
done
```

### 3. Extract to OCaml

```bash
# Z-based extraction (recommended)
coqc -Q . KeenKenning ExtractZ.v

# Minimal nat-based extraction (for algorithms only)
coqc -Q . KeenKenning ExtractMinimal.v
```

### 4. Compile OCaml with ocamlopt

```bash
# Compile extracted OCaml
ocamlfind ocamlopt -package stdlib -c latin_z.mli
ocamlfind ocamlopt -package stdlib -c latin_z.ml

# Compile production OCaml
ocamlfind ocamlopt -c latin_production.ml
```

### 5. Generate C Code

Two options:

**Option A: Manual translation (current approach)**
- Read extracted OCaml
- Translate algorithm structure to C
- Preserve invariants from Rocq proofs

**Option B: OCaml-C FFI**
```bash
# Compile OCaml to native library
ocamlfind ocamlopt -output-obj -package stdlib \
  latin_production.ml -o latin_production.o

# Link with C code via OCaml runtime
```

## File Summary

| File | Purpose | Status |
|------|---------|--------|
| `LatinEnum.v` | Latin square enumeration theorems | Verified |
| `LatinSquare.v` | Latin square properties | Verified |
| `Modes.v` | Game mode specifications | Verified |
| `DLX.v` | Dancing Links algorithm | Verified |
| `SAT.v` | SAT encoding correctness | Verified |
| `LatinBoundsZ.v` | Z-based bounds (extraction-friendly) | Verified |
| `ExtractZ.v` | Z-based extraction configuration | Works |
| `ExtractMinimal.v` | Minimal nat-based extraction | Works |
| `latin_z.ml` | Extracted OCaml (Z-based) | Compiles |
| `latin_minimal.ml` | Extracted OCaml (minimal) | Compiles |
| `latin_production.ml` | Hand-optimized OCaml | Compiles |
| `keen_verified.c` | C implementation with verified bounds | In use |
| `latin_verified.c` | C Latin square validation | In use |

## Verification Status

### Rocq Proofs (coqchk verified)

| Module | Key Theorems |
|--------|--------------|
| LatinEnum | `latin_3x3_count`, `bitwise_increases_ambiguity` |
| LatinSquare | Row/column uniqueness |
| Modes | `mode_flags_valid`, `classik_subset_kenning` |
| DLX | Cover/uncover correctness |
| SAT | CNF clause generation soundness |

### Z3 SMT Verification

| Specification | Result |
|---------------|--------|
| LatinSquare4x4.smt2 | SAT (valid solution found) |
| LatinSquareSMT.smt2 | UNSAT (constraint correctness) |

## Best Practices

### 1. Avoid Large Literals in Rocq

```coq
(* BAD: Triggers unary representation *)
Definition big_const := 812851200.

(* GOOD: Compute from smaller values *)
Definition big_const := fact 6 * fact 5 * 9408.

(* BETTER: Use Z type directly *)
Definition big_const_z : Z := 812851200.
```

### 2. Use Z for Constants, nat for Algorithms

```coq
(* Z for large constants *)
Definition MODE_BITWISE : Z := 2048.

(* nat for recursive algorithms (easier proofs) *)
Fixpoint stirling2 (n k : nat) : nat := ...
```

### 3. Verify Before Production

```bash
# Always run coqchk after changes
coqchk -Q . KeenKenning KeenKenning.YourModule

# Run static analysis on C code
cppcheck --enable=all formal/*.c
```

### 4. Test Extracted Code

```bash
# Quick OCaml test
ocaml -stdin <<'EOF'
#use "latin_production.ml";;
Printf.printf "fact 6 = %d\n" (fact 6);;
Printf.printf "latin_count 6 = %d\n" (latin_count 6);;
EOF
```

## Troubleshooting

### "Dynlink error: implementation mismatch"

Use isolated opam switch:
```bash
eval $(opam env --switch=rocq-isolated)
```

### "Stack overflow" during vm_compute

Avoid computing large values at proof time:
```coq
(* BAD *)
Lemma big_value : latin_count 6 = 812851200.
Proof. native_compute. reflexivity. Qed.

(* GOOD: Use algebraic proof instead *)
Lemma big_value : latin_count 6 = fact 6 * fact 5 * reduced_count 6.
Proof. reflexivity. Qed.
```

### Extracted OCaml has uint types

Use Z-based extraction (ExtractZ.v) instead of nat-based extraction.

## References

- [Rocq Extraction Documentation](https://rocq-prover.org/doc/V8.18.0/refman/addendum/extraction.html)
- [ExtrOcamlZInt Module](https://rocq-prover.org/doc/v8.9/stdlib/Coq.extraction.ExtrOcamlZInt.html)
- [Pierre Letouzey: Extraction in Coq](https://www.irif.fr/~letouzey/download/letouzey_extr_cie08.pdf)
- [Software Foundations: Extraction](https://softwarefoundations.cis.upenn.edu/lf-current/Extraction.html)

---

*Generated as part of KeenKenning formal verification toolchain*
