# Formal Verification Toolchain for KeenKenning

## Overview

This document describes the formal verification tools installed and configured for the KeenKenning project.

## Opam Switch Configuration

**Switch Name:** `rocq-isolated`
**OCaml Version:** 5.2.1 (opam-managed, isolated from system)
**Rocq Version:** 9.0.1 (compatible with all installed packages)

**Important:** The isolated opam switch was created to avoid the known issue with OCaml 5 + system ocamlfind installations, which causes "Dynlink error: implementation mismatch" when loading plugins.

### Activation

```bash
eval $(opam env --switch=rocq-isolated)
```

## Installed Packages

### Core Rocq/Coq Stack

| Package | Version | Description |
|---------|---------|-------------|
| rocq-core | 9.0.1 | The Rocq Prover with its prelude |
| rocq-runtime | 9.0.1 | Core Binaries and Tools |
| rocq-stdlib | 9.0.0 | Standard Library |
| coq-core | 9.0.1 | Compatibility binaries |
| coq-stdlib | 9.0.0 | Compatibility stdlib |

### Mathematical Components (mathcomp)

| Package | Version | Description |
|---------|---------|-------------|
| rocq-mathcomp-boot | 2.5.0 | Small Scale Reflection |
| rocq-mathcomp-order | 2.5.0 | Order theory |
| rocq-mathcomp-ssreflect | 2.5.0 | SSReflect compatibility |
| rocq-mathcomp-algebra | 2.5.0 | Algebra library |
| rocq-mathcomp-fingroup | 2.5.0 | Finite groups |
| rocq-mathcomp-solvable | 2.5.0 | Finite groups (II) |
| rocq-mathcomp-field | 2.5.0 | Fields library |

### Hierarchy Builder & Elpi

| Package | Version | Description |
|---------|---------|-------------|
| rocq-hierarchy-builder | 1.10.1 | Packed class hierarchies |
| rocq-elpi | 3.2.0 | Elpi extension language |
| elpi | 3.4.2 | Embeddable lambdaProlog Interpreter |

### Extended Libraries

| Package | Version | Description |
|---------|---------|-------------|
| coq-stdpp | 1.12.0 | Extended Standard Library (Iris) |
| coq-ext-lib | 0.13.0 | Definitions, theorems, tactics |
| coq-simple-io | 1.11.0 | IO monad for Coq |

### Testing Tools

| Package | Version | Description |
|---------|---------|-------------|
| coq-quickchick | 2.1.1 | Property-Based Testing |

## System Tools

### TLA+ (Temporal Logic of Actions)

| Tool | Version | Description |
|------|---------|-------------|
| tla-plus-toolbox | 1.7.4 | Integrated Development Environment |
| tlc | (bundled) | Model checker for TLA+ specifications |

**Location:** `/usr/bin/tlc`

### Z3 Theorem Prover

| Tool | Version | Description |
|------|---------|-------------|
| z3-git | 4.15.4 | SMT solver from Microsoft Research |
| python-z3-solver | 4.12.0 | Python bindings for Z3 |

**Location:** `/usr/bin/z3`
**Version:** Z3 4.15.5 - 64 bit

## Usage Examples

### Compile a file using mathcomp and elpi

```bash
eval $(opam env --switch=rocq-isolated)
coqc -Q . KeenKenning file.v
```

### Example proof using mathcomp ssreflect

```coq
From elpi Require Import elpi.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

Lemma test_lemma (b : bool) : b || ~~b.
Proof. by case: b. Qed.
```

### Using QuickChick for property testing

```coq
From QuickChick Require Import QuickChick.

Derive Arbitrary for nat.

QuickCheck (fun n : nat => n <= n + 0).
```

### Using stdpp

```coq
From stdpp Require Import base decidable.

Lemma test_decide (P : Prop) `{Decision P} : P \/ ~P.
Proof. destruct (decide P); auto. Qed.
```

## Verification Pipeline

For KeenKenning formal verification:

1. **Compile Rocq Proofs:** `coqc -Q . KeenKenning *.v`
2. **Independent Check:** `coqchk -Q . KeenKenning Module.Name`
3. **Extract OCaml:** `coqc Extract.v` (if using extraction)
4. **Property Testing:** Use QuickChick for randomized testing
5. **SMT Solving:** Use Z3 for constraint satisfaction

## Troubleshooting

### "Dynlink error: implementation mismatch"

This error occurs when system OCaml libraries conflict with opam libraries.

**Solution:** Use the isolated opam switch:
```bash
eval $(opam env --switch=rocq-isolated)
```

### "Cannot find a physical path bound to logical path"

This occurs when COQLIB is not set correctly.

**Solution:** Ensure the opam environment is activated and coqc points to the opam switch:
```bash
which coqc  # Should show ~/.opam/rocq-isolated/bin/coqc
coqc --config | grep COQLIB  # Should show opam path
```

## References

- [Rocq Prover Documentation](https://rocq-prover.org/docs/)
- [Mathematical Components](https://math-comp.github.io/)
- [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder)
- [QuickChick](https://github.com/QuickChick/QuickChick)
- [stdpp (Iris)](https://gitlab.mpi-sws.org/iris/stdpp)
- [TLA+ Tools](https://lamport.azurewebsites.net/tla/tools.html)
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3)
