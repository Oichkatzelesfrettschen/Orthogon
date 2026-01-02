# Formal Verification Makefile
# KeenKenning Project
# SPDX-License-Identifier: MIT

# =============================================================================
# Switch Configuration
# =============================================================================
# Main development: rocq-9.1.0 (OCaml 5.4.0 + Rocq 9.1.0)
# Verified extraction: keen-verified (OCaml 4.14.2 + Rocq 9.0.0)
#
# The Makefile enforces switch usage to prevent PATH-based surprises.
# =============================================================================

OPAM_SWITCH_MAIN := rocq-9.1.0
OPAM_SWITCH_VERIFIED := keen-verified
OPAM := opam

# Rocq 9.1.0 compiler with switch enforcement
ROCQC = $(OPAM) exec --switch=$(OPAM_SWITCH_MAIN) -- rocq compile
ROCQFLAGS = -Q . KeenKenning -w +default

# Verified extraction uses Rocq 9.0.0 (required by rocq-verified-extraction)
ROCQC_VERIFIED = $(OPAM) exec --switch=$(OPAM_SWITCH_VERIFIED) -- rocq compile
CC = cc
CFLAGS = -Wall -Wextra -Werror -std=c23 -I../app/src/main/jni
Z3 = z3

# JNI directory (for dlx.c)
JNI_DIR = ../app/src/main/jni

# =============================================================================
# Coq/Rocq Sources (order matters for dependencies)
# =============================================================================

# Core specification files (verified with Rocq 9.1.0)
SPEC_SOURCES = SolverTypes.v DSF.v CageOps.v LatinSquare.v Modes.v \
               DLX.v SAT.v SolverSpec.v GeneratorSpec.v

# Extraction files (legacy OCaml extraction)
EXTRACT_SOURCES = Extraction.v ExtractSolver.v

# All Coq sources for main build
COQ_SOURCES = $(SPEC_SOURCES) $(EXTRACT_SOURCES)
COQ_VOS = $(COQ_SOURCES:.v=.vo)
COQ_GLOBS = $(COQ_SOURCES:.v=.glob)

# Verified extraction (requires Rocq 9.0.0 + rocq-verified-extraction)
VERIFIED_EXTRACT_SOURCES = VerifiedExtraction.v

# Extracted OCaml
OCAML_FILES = DLX.ml DLX.mli LatinSquare.ml LatinSquare.mli SAT.ml SAT.mli

# C implementation (verified + bridge + latin wrapper + JNI interface)
C_SOURCES = keen_verified.c dlx_latin_bridge.c latin_verified.c keen_verified_jni.c
C_HEADERS = keen_verified.h z3_cage_solver.h dlx_latin_bridge.h latin_verified.h keen_verified_jni.h
C_OBJECTS = keen_verified.o dlx_latin_bridge.o latin_verified.o keen_verified_jni.o dlx.o

# SMT files
SMT_FILES = LatinSquareSMT.smt2 LatinSquare4x4.smt2

# Test binaries
TEST_BIN = test_dlx_latin
TEST_COMPREHENSIVE = test_comprehensive
TEST_VERIFIED = test_latin_verified
TEST_JNI = test_jni_interface

.PHONY: all clean coq extract c verify test integration-test comprehensive-test \
        verified-test jni-test all-tests check-switch check-switches specs \
        verified-extract

# =============================================================================
# Switch Verification
# =============================================================================

# Check main switch exists and has required packages
check-switch:
	@$(OPAM) switch show --switch=$(OPAM_SWITCH_MAIN) >/dev/null 2>&1 || \
		(echo "ERROR: Switch $(OPAM_SWITCH_MAIN) not found. Create with:" && \
		 echo "  opam switch create $(OPAM_SWITCH_MAIN) 5.4.0" && \
		 echo "  opam install rocq-prover" && exit 1)
	@$(OPAM) exec --switch=$(OPAM_SWITCH_MAIN) -- rocq --version | grep -q "9.1.0" || \
		(echo "ERROR: Rocq 9.1.0 not found in $(OPAM_SWITCH_MAIN)" && exit 1)
	@echo "Switch $(OPAM_SWITCH_MAIN) verified: Rocq 9.1.0"

# Check verified extraction switch
check-switch-verified:
	@$(OPAM) switch show --switch=$(OPAM_SWITCH_VERIFIED) >/dev/null 2>&1 || \
		(echo "ERROR: Switch $(OPAM_SWITCH_VERIFIED) not found." && exit 1)
	@$(OPAM) exec --switch=$(OPAM_SWITCH_VERIFIED) -- rocq --version | grep -q "9.0.0" || \
		(echo "WARNING: Rocq 9.0.0 expected in $(OPAM_SWITCH_VERIFIED)" && exit 1)
	@echo "Switch $(OPAM_SWITCH_VERIFIED) verified: Rocq 9.0.0"

check-switches: check-switch check-switch-verified
	@echo "All switches verified"

# =============================================================================
# Main Targets
# =============================================================================

all: check-switch coq extract c

# Compile Coq specifications
coq: $(COQ_VOS)

%.vo: %.v
	$(ROCQC) $(ROCQFLAGS) $<

# =============================================================================
# Dependencies
# =============================================================================

# Core type dependencies
DSF.vo: SolverTypes.vo
CageOps.vo: SolverTypes.vo
Modes.vo: SolverTypes.vo

# Latin square solver
DLX.vo: LatinSquare.vo
SAT.vo: LatinSquare.vo
SolverSpec.vo: SolverTypes.vo DSF.vo CageOps.vo LatinSquare.vo
GeneratorSpec.vo: SolverSpec.vo

# Extraction
Extraction.vo: LatinSquare.vo DLX.vo SAT.vo
ExtractSolver.vo: SolverSpec.vo GeneratorSpec.vo

# Specs-only target (no extraction)
specs: check-switch $(SPEC_SOURCES:.v=.vo)
	@echo "All specifications compiled"

# Extract to OCaml
extract: Extraction.vo
	@echo "OCaml files extracted"
	@ls -la $(OCAML_FILES) 2>/dev/null || true

# Compile C implementation
c: $(C_OBJECTS)

keen_verified.o: keen_verified.c keen_verified.h
	$(CC) $(CFLAGS) -c $< -o $@

dlx_latin_bridge.o: dlx_latin_bridge.c dlx_latin_bridge.h keen_verified.h
	$(CC) $(CFLAGS) -c $< -o $@

latin_verified.o: latin_verified.c latin_verified.h dlx_latin_bridge.h keen_verified.h
	$(CC) $(CFLAGS) -c $< -o $@

keen_verified_jni.o: keen_verified_jni.c keen_verified_jni.h latin_verified.h
	$(CC) $(CFLAGS) -c $< -o $@

dlx.o: $(JNI_DIR)/dlx.c $(JNI_DIR)/dlx.h
	$(CC) $(CFLAGS) -c $< -o $@

# Build integration test
$(TEST_BIN): $(C_OBJECTS) test_dlx_latin.c
	$(CC) $(CFLAGS) -o $@ test_dlx_latin.c $(C_OBJECTS)

# Verify SMT files with Z3
verify: $(SMT_FILES)
	@echo "Verifying 4x4 Latin square encoding..."
	$(Z3) LatinSquare4x4.smt2

# Run basic tests
test: c verify
	@echo "All basic tests passed"

# Run integration test (DLX + verified functions)
integration-test: $(TEST_BIN)
	@echo "Running DLX Latin square integration test..."
	./$(TEST_BIN)

# Build comprehensive test
$(TEST_COMPREHENSIVE): $(C_OBJECTS) test_comprehensive.c
	$(CC) $(CFLAGS) -o $@ test_comprehensive.c $(C_OBJECTS) -lm

# Run comprehensive test (all sizes 2-16)
comprehensive-test: $(TEST_COMPREHENSIVE)
	@echo "Running comprehensive grid size tests..."
	./$(TEST_COMPREHENSIVE) 12

# Build latin_verified test
$(TEST_VERIFIED): $(C_OBJECTS) test_latin_verified.c
	$(CC) $(CFLAGS) -o $@ test_latin_verified.c $(C_OBJECTS) -lm

# Run verified latin generator test
verified-test: $(TEST_VERIFIED)
	@echo "Running verified Latin generator tests..."
	./$(TEST_VERIFIED)

# Build JNI interface test
$(TEST_JNI): $(C_OBJECTS) test_jni_interface.c
	$(CC) $(CFLAGS) -o $@ test_jni_interface.c $(C_OBJECTS) -lm

# Run JNI interface test
jni-test: $(TEST_JNI)
	@echo "Running JNI interface tests..."
	./$(TEST_JNI)

# Run all tests
all-tests: integration-test comprehensive-test verified-test jni-test
	@echo "All test suites completed!"

# =============================================================================
# Verified Extraction (Rocq 9.0.0 + rocq-verified-extraction)
# =============================================================================

# Compile VerifiedExtraction.v using the verified extraction switch
# This produces Malfunction IR files for verified compilation
verified-extract: check-switch-verified
	@echo "Running verified extraction with Rocq 9.0.0..."
	$(ROCQC_VERIFIED) $(ROCQFLAGS) VerifiedExtraction.v
	@echo "Verified extraction complete"
	@ls -la extracted/*.mlf 2>/dev/null || echo "(No .mlf files yet)"

# Compile Malfunction to native objects
MALC = malfunction
extracted/%.o: extracted/%.mlf
	$(MALC) compile $< -o $@

# =============================================================================
# Cleanup
# =============================================================================

# Clean generated files
clean:
	rm -f $(COQ_VOS) $(COQ_GLOBS)
	rm -f $(OCAML_FILES)
	rm -f $(C_OBJECTS)
	rm -f $(TEST_BIN) $(TEST_COMPREHENSIVE) $(TEST_VERIFIED) $(TEST_JNI)
	rm -f .*.aux *.aux
	rm -f VerifiedExtraction.vo VerifiedExtraction.glob

clean-extracted:
	rm -f extracted/*.ml extracted/*.mli extracted/*.mlf extracted/*.o

clean-all: clean clean-extracted

# =============================================================================
# Statistics
# =============================================================================

# Show statistics
stats:
	@echo "=== Coq Specifications ==="
	@wc -l $(COQ_SOURCES)
	@echo ""
	@echo "=== Extracted OCaml ==="
	@wc -l $(OCAML_FILES) 2>/dev/null || echo "(not yet extracted)"
	@echo ""
	@echo "=== C Implementation ==="
	@wc -l $(C_SOURCES) $(C_HEADERS)
	@echo ""
	@echo "=== Integration Bridge ==="
	@wc -l dlx_latin_bridge.c dlx_latin_bridge.h
