# Coq/Rocq Binary Reference

This document describes all Coq binaries installed on the system and how they are used for KeenKenning formal verification.

## System Information

| Property | Value |
|----------|-------|
| Version | Rocq 9.1.0 |
| OCaml | 5.4.0 |
| Package | `rocq` (Arch Linux) |

## Binary Reference

### Core Compilation

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coqc` | **Compiler** - Compile .v to .vo | `coqc -Q . KeenKenning File.v` |
| `coqtop` | Interactive toplevel (REPL) | `coqtop -Q . KeenKenning` |
| `coqtop.byte` | Bytecode version of toplevel | Same as coqtop, slower but debuggable |
| `rocq` | New name for coqtop | `rocq -Q . KeenKenning` |
| `rocq.byte` | Bytecode version | Same as rocq |

### Verification & Checking

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coqchk` | **Independent proof checker** - Verifies .vo files | `coqchk -Q . KeenKenning Module.Name` |
| `rocqchk` | New name for coqchk | Same as coqchk |

**CRITICAL**: Always run `coqchk` after compilation to independently verify proofs are valid.

### Build System

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coq_makefile` | Generate Makefile for Coq project | `coq_makefile -Q . Pkg *.v -o Makefile.coq` |
| `coqdep` | Dependency analysis | `coqdep -Q . Pkg *.v` |
| `coqworkmgr` | Parallel compilation worker manager | Automatic with `make -j` |

### Documentation

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coqdoc` | Generate HTML/LaTeX docs from .v | `coqdoc -Q . Pkg --html -d docs/ File.v` |
| `coq-tex` | Embed Coq in LaTeX documents | `coq-tex paper.tex` |

### Analysis & Inspection

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coqwc` | Word count / metrics | `coqwc *.v` |
| `votour` | Inspect .vo file structure | `votour File.vo` |

### Specialized

| Binary | Purpose | Usage |
|--------|---------|-------|
| `coqnative` | Native compilation (disabled in Arch) | N/A |
| `coqpp` | Preprocessor for Ltac2/plugins | Plugin development |
| `csdpcert` | SDP certificate checker | Micromega proofs |
| `ocamllibdep` | OCaml library dependencies | Plugin development |

## KeenKenning Verification Pipeline

```
1. COMPILE       coqc -Q . KeenKenning *.v
2. VERIFY        coqchk -Q . KeenKenning KeenKenning.Module
3. EXTRACT       coqc Extract.v (generates .ml)
4. METRICS       coqwc *.v
5. DOCUMENT      coqdoc --html -d docs/coq *.v
```

## Warning Flags

Standard compilation with balanced warnings:
```bash
coqc -w -deprecated-transitive-library-file,-abstract-large-number,-native-compiler-disabled \
     -Q . KeenKenning File.v
```

| Warning | Meaning | Action |
|---------|---------|--------|
| `deprecated-transitive-library-file` | Stdlib 9.0 import changes | Suppress |
| `abstract-large-number` | Large nat literals | Suppress |
| `native-compiler-disabled` | vm_compute fallback | Suppress |
| `non-recursive` | Fixpoint doesn't recurse | Refactor to Definition |

## KeenKenning Formal Specifications

| File | Lines | Purpose | Key Theorems |
|------|-------|---------|--------------|
| `Modes.v` | 291 | Mode flag specifications | `mode_flags_valid`, `classik_subset_kenning` |
| `LatinEnum.v` | 296 | Latin square enumeration | `latin_3x3_count`, `constraint_expansion_needed` |
| `LatinSquare.v` | 272 | Latin square properties | Row/column validity |
| `DLX.v` | 277 | Dancing Links algorithm | Cover/uncover correctness |
| `SAT.v` | 267 | SAT encoding | CNF clause generation |

## Metrics Summary

```
     spec    proof comments
      863      156      414 total
```

## Verification Status

| Module | coqc | coqchk | Status |
|--------|------|--------|--------|
| KeenKenning.Modes | PASS | PASS | Verified |
| KeenKenning.LatinEnum | PASS | PASS | Verified |
| KeenKenning.LatinSquare | PASS | - | Compiled |
| KeenKenning.DLX | PASS | - | Compiled |
| KeenKenning.SAT | PASS | - | Compiled |

## Installing Additional Coq Packages

Check available packages:
```bash
pacman -Ss coq
yay -Ss coq
```

Useful packages (not currently installed):
- `coq-mathcomp` - Mathematical Components library
- `coq-equations` - Dependent pattern matching
- `coq-flocq` - Floating point formalization
