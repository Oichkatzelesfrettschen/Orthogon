# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Android Keen puzzle game (KenKen-style) with two product flavors:
- **Keen Classik**: Traditional mode (3x3-9x9 grids, no ML) - `app/src/classik/`
- **Keen Kenning**: Advanced mode (3x3-16x16 grids, ML-enabled) - `app/src/kenning/`

Package: `org.yegie.keenkenning` (with `.classik` or `.kenning` suffix per flavor)

## Build Commands
- **Build Debug:** `./gradlew assembleKenningDebug`
- **Build Release:** `./gradlew assembleKenningRelease`
- **Clean Build:** `./gradlew clean assembleKenningDebug`
- **Run Unit Tests:** `./gradlew testKenningDebugUnitTest`
- **Run InstrumentedTests:** `./gradlew connectedKenningDebugAndroidTest`
- **Lint:** `./gradlew lintKenningDebug`
- **Format Kotlin:** `./gradlew ktlintFormat`
- **Format C/C++:** `find app/src/main/jni -name "*.[ch]" -exec clang-format -i {} +`

## Code Style
- **Kotlin:** Follows strict Kotlin coding conventions (ktlint enforced).
  - Use `val` over `var` where possible.
  - Data classes for models.
  - Sealed classes for state.
  - `allWarningsAsErrors = true` is enabled.
- **Rocq/Coq:**
  - **Version:** Rocq 9.1.0 (Coq-compatible prover)
  - **Compliance:** Warnings as errors (`-w +default` in Makefile)
  - **Deprecated syntax:** Always update to latest Stdlib conventions
  - **Proofs:** Must complete with `Qed`, not `Admitted`
  - **Build:** `make` in `formal/` directory
- **C/C++:**
  - **Standard:** ISO/IEC 9899:2023 (C23) and ISO/IEC 14882:2023 (C++23).
  - **Compliance:** Strict "Warnings as Errors" (`-Werror -Wall -Wextra`).
  - **Formatting:** Google Style (Clang-Format).
  - **Conventions:**
    - Use `bool`, `true`, `false` (stdbool.h not required in C23).
    - Use `nullptr` instead of `NULL`.
    - Explicit casts for all arithmetic conversions (`size_t`, `int`, `char`).
    - Mark unused functions/params with `[[maybe_unused]]`.
    - No GNU extensions (`CMAKE_C_EXTENSIONS OFF`).

## Architecture

```
Compose UI (GameScreen.kt, MenuScreen.kt)
    |
ViewModel Layer (GameViewModel.kt)
    |
Data Layer (data/*.kt - 10 files)
    |
Integration Layer (KeenModelBuilder.java, PuzzleGenerator.kt)
    |
    +-- JNI Bridge (keen-android-jni.c)
    |       |
    |       +-- Native C Layer (keen.c, latin.c, dlx.c, tree234.c)
    |
    +-- ONNX Runtime (NeuralKeenGenerator.java) [Kenning flavor only]
            |
            +-- latin_solver.onnx (3x3-16x16 grids)
```

### Key Layers

**JNI Bridge**: `KeenModelBuilder.java` calls native methods that return structured responses:
- Success: `"OK:payload_data"`
- Error: `"ERR:code:message"`
- JNI functions in `keen-android-jni.c` follow naming: `Java_org_yegie_keenkenning_<Class>_<Method>`

**Puzzle Payload Format**: Zone indices + zone definitions + solution digits
```
"00,00,01,00,02,01;a00006,m00002,s00001,123456789"
 ^-- zone indices   ^-- zones (op+value)  ^-- solution
```

**AI Generation Flow** (Kenning flavor):
1. `NeuralKeenGenerator.generate()` runs ONNX inference
2. Returns `int[]` Latin square grid
3. `KeenModelBuilder` passes grid to C via `getLevelFromAI()`
4. C layer generates cages/clues for the AI grid
5. Falls back to pure C generation if AI fails validation

### Game Modes (11 total)

Modes use bit flags passed to native layer via `modeFlags` parameter:
```kotlin
STANDARD           = 0x00   // All operations
MULTIPLICATION_ONLY = 0x01   // Only multiplication
MYSTERY            = 0x02   // Hidden operations
ZERO_INCLUSIVE     = 0x04   // Range 0 to N-1
NEGATIVE_NUMBERS   = 0x08   // Range -N to +N
EXPONENT           = 0x10   // Includes ^ operator
MODULAR            = 0x20   // Wrap-around arithmetic
KILLER             = 0x40   // No repeated digits in cages
```

Mode definitions: `app/src/main/java/org/yegie/keenkenning/data/GameMode.kt`

## Testing

**Unit Tests** (`app/src/test/`):
- `PuzzleParserTest.kt` - Payload parsing
- `JniResultParserTest.kt` - Error handling
- `GameViewModelTest.kt` - State management
- `PuzzleInvariantsTest.kt` - Generation constraints
- `DeterministicSeedingTest.kt` - Reproducibility

Run specific tests:
```bash
./gradlew testDebugUnitTest --tests "*PuzzleParser*"
./gradlew testDebugUnitTest --tests "*.data.*"  # All data layer tests
```

**Instrumented Tests** (`app/src/androidTest/`):
- `AiIntegrationTest.kt` - ONNX model loading on device

## ML Pipeline

Located in `scripts/ai/`:

```bash
# Generate training data (CUDA, 1.14M grids)
make generate-data-cuda

# Train model (autoregressive transformer, 60 epochs)
make train

# Quick test training (5 epochs)
make train-quick

# Resume from checkpoint
make train-resume

# Deploy trained model to assets
make deploy-model

# Full pipeline: generate -> train -> deploy -> build APK
make full-pipeline
```

Model outputs to `scripts/ai/latin_solver.onnx`, deployed to `app/src/kenning/assets/`.

Training script: `scripts/ai/train_autoregressive.py` (6.4M parameter transformer with curriculum learning)

## Formal Verification

Located in `formal/`:

```bash
# Build all Rocq proofs
cd formal && make

# Clean and rebuild
cd formal && make clean && make

# Check specific module
cd formal && rocq compile SolverTypes.v
```

**Verified Modules** (Rocq 9.1.0):

| Module | Status | Proven | Admitted | Description |
|--------|--------|--------|----------|-------------|
| SolverTypes.v | Phase 1 Done | 6 | 1 | Core types + latin soundness |
| DSF.v | Partial | 8 | 3 | Disjoint Set Forest (Union-Find) |
| CageOps.v | Phase 1 Done | 17 | 0 | Cage operation evaluation |
| DLX.v | Complete | 2 | 0 | Dancing Links exact cover |
| SAT.v | Complete | 1 | 0 | CNF encoding |
| LatinSquare.v | Complete | 2 | 2 | Latin square constraints |

**Key Proven Theorems**:
- `latin_constraint_sound` - Valid Latin grid cells contain valid digits
- `canonify_is_root` - DSF canonify returns root elements
- `cage_satisfiedb_reflect` - Boolean/Prop equivalence for cage satisfaction
- `dsf_init_wf` - Initial DSF is well-formed
- `dsf_equiv_refl/sym/trans` - DSF equivalence is an equivalence relation

**Extraction Strategy**:
- Current: Standard OCaml extraction + hand-written C bridge
- Future: rocq-verified-extraction for reduced TCB (Phase 2)
- C bridge: `formal/keen_verified.c` (~2500 LOC)
- JNI integration: `formal/keen_verified_jni.c`

See `formal/PHASE_PLAN_UPDATED.md` for detailed verification roadmap.

## Native Development

**Source files**: `app/src/main/jni/`

| File | Purpose |
|------|---------|
| `keen-android-jni.c` | JNI entry points |
| `keen.c` | Puzzle generation, cage creation |
| `latin.c` | Latin square solver |
| `dlx.c` | Dancing Links algorithm |
| `keen_hints.c` | Constraint propagation for hints |
| `keen_validate.c` | Solution validation |

**Compiler flags** (CMakeLists.txt):
```
-Wall -Wextra -Werror
-Wno-unused-parameter -Wno-sign-compare
-Wno-missing-field-initializers -Wno-unused-function
```

**ABIs**: arm64-v8a, armeabi-v7a, x86, x86_64, riscv64

## Standards

- **Warnings as errors**: Lint `warningsAsErrors = true`, Java `-Xlint:all -Werror`
- **Internal naming**: Use "Keen" prefix (not "KenKen" - trademarked)
- **JNI naming**: `Java_org_yegie_keenkenning_<Class>_<Method>` (underscored package path)
- **Native library**: Must be `libkeen-android-jni.so` (matches CMakeLists.txt)
- **JDK**: 21 required (Gradle 8.6 incompatible with JDK 25)

## Flavor Configuration

Defined in `app/build.gradle`:

| Flavor | MAX_GRID_SIZE | ML_ENABLED | App ID Suffix |
|--------|---------------|------------|---------------|
| classik | 9 | false | .classik |
| kenning | 16 | true | .kenning |

Access via `BuildConfig.MAX_GRID_SIZE`, `BuildConfig.ML_ENABLED`.

## CI/CD

GitHub Actions workflows:
- `android-release.yml` - Build, lint, test, package APKs
- `native-sanitizers.yml` - AddressSanitizer/UBSan on JNI changes

Triggered on push to main and PRs touching `app/src/main/jni/**`.

## Common Issues

1. **JDK mismatch**: Gradle 8.6 requires JDK 21, fails with 25
2. **JNI null returns**: Check `KeenModelBuilder.getLastJniError()` for native errors
3. **Mode size limits**: Zero/Negative/Modular modes limited to 9x9 (stability)
4. **ONNX loading**: Kenning flavor only; test on device via `AiIntegrationTest`

## References

- @docs/SYNTHESIS_REPORT.md - Build harmonization
- @docs/GAME_MODES_ARCHITECTURE.md - Mode implementation details
- @scripts/ai/README.md - ML pipeline documentation
- @formal/PHASE_PLAN_UPDATED.md - Formal verification roadmap
- @formal/EXTRACTION_COMPARISON.md - Extraction strategy analysis
