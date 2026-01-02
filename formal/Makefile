# Formal Verification Makefile
# KeenKenning Project
# SPDX-License-Identifier: MIT

COQC = coqc
COQFLAGS = -Q . KeenKenning -w +default
CC = cc
CFLAGS = -Wall -Wextra -Werror -std=c23 -I../app/src/main/jni
Z3 = z3

# JNI directory (for dlx.c)
JNI_DIR = ../app/src/main/jni

# Coq sources (order matters for dependencies)
COQ_SOURCES = LatinSquare.v DLX.v SAT.v Extraction.v
COQ_VOS = $(COQ_SOURCES:.v=.vo)
COQ_GLOBS = $(COQ_SOURCES:.v=.glob)

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

.PHONY: all clean coq extract c verify test integration-test comprehensive-test verified-test jni-test all-tests

all: coq extract c

# Compile Coq specifications
coq: $(COQ_VOS)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# Dependencies
DLX.vo: LatinSquare.vo
SAT.vo: LatinSquare.vo
Extraction.vo: LatinSquare.vo DLX.vo SAT.vo

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

# Clean generated files
clean:
	rm -f $(COQ_VOS) $(COQ_GLOBS)
	rm -f $(OCAML_FILES)
	rm -f $(C_OBJECTS)
	rm -f $(TEST_BIN) $(TEST_COMPREHENSIVE) $(TEST_VERIFIED) $(TEST_JNI)
	rm -f .*.aux *.aux

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
