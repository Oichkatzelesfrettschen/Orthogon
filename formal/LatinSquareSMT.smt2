; Latin Square and KenKen Cage Constraint SMT Encoding
; Author: KeenKenning Project
; Date: 2026-01-01
; SPDX-License-Identifier: MIT
;
; This file provides an SMT-LIB2 encoding for Latin square constraints
; and KenKen cage arithmetic, suitable for Z3 solver integration.

; ============================================================================
; SECTION 1: Parameterized Latin Square Constraints
; ============================================================================

; For a 4x4 example grid (parameterize N for different sizes)
(declare-const N Int)
(assert (= N 4))

; Cell values: cell[r][c] represents value at row r, column c
; Values are in range [1, N]
(declare-fun cell (Int Int) Int)

; Valid cell bounds
(define-fun valid-cell ((r Int) (c Int)) Bool
  (and (>= r 0) (< r N) (>= c 0) (< c N)))

; Value range constraint: all cells contain values 1 to N
(assert (forall ((r Int) (c Int))
  (=> (valid-cell r c)
      (and (>= (cell r c) 1) (<= (cell r c) N)))))

; Row uniqueness: no repeated values in any row
(assert (forall ((r Int) (c1 Int) (c2 Int))
  (=> (and (valid-cell r c1) (valid-cell r c2) (not (= c1 c2)))
      (not (= (cell r c1) (cell r c2))))))

; Column uniqueness: no repeated values in any column
(assert (forall ((r1 Int) (r2 Int) (c Int))
  (=> (and (valid-cell r1 c) (valid-cell r2 c) (not (= r1 r2)))
      (not (= (cell r1 c) (cell r2 c))))))

; ============================================================================
; SECTION 2: Cage Constraint Encoding Helpers
; ============================================================================

; Addition cage: sum of cells equals target
(define-fun cage-add-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (= (+ (cell r1 c1) (cell r2 c2)) target))

(define-fun cage-add-3 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (target Int)) Bool
  (= (+ (cell r1 c1) (cell r2 c2) (cell r3 c3)) target))

(define-fun cage-add-4 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (r4 Int) (c4 Int) (target Int)) Bool
  (= (+ (cell r1 c1) (cell r2 c2) (cell r3 c3) (cell r4 c4)) target))

; Multiplication cage: product of cells equals target
(define-fun cage-mul-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (= (* (cell r1 c1) (cell r2 c2)) target))

(define-fun cage-mul-3 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (target Int)) Bool
  (= (* (cell r1 c1) (cell r2 c2) (cell r3 c3)) target))

; Subtraction cage: |a - b| = target (order-independent)
(define-fun cage-sub-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (or (= (- (cell r1 c1) (cell r2 c2)) target)
      (= (- (cell r2 c2) (cell r1 c1)) target)))

; Division cage: a/b = target OR b/a = target (integer division, exact)
(define-fun cage-div-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (or (and (= (mod (cell r1 c1) (cell r2 c2)) 0)
           (= (div (cell r1 c1) (cell r2 c2)) target))
      (and (= (mod (cell r2 c2) (cell r1 c1)) 0)
           (= (div (cell r2 c2) (cell r1 c1)) target))))

; ============================================================================
; SECTION 3: Extended Mode Constraints
; ============================================================================

; XOR cage (BITWISE mode): XOR of cell values equals target
; Note: Z3 supports bvxor for bitvectors, but for integers we use a helper
(define-fun int-xor ((a Int) (b Int)) Int
  (bv2int (bvxor ((_ int2bv 32) a) ((_ int2bv 32) b))))

(define-fun cage-xor-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (= (int-xor (cell r1 c1) (cell r2 c2)) target))

(define-fun cage-xor-3 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (target Int)) Bool
  (= (int-xor (int-xor (cell r1 c1) (cell r2 c2)) (cell r3 c3)) target))

; Modular cage (MODULAR mode): sum mod N equals target
(define-fun cage-mod-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (target Int)) Bool
  (= (mod (+ (cell r1 c1) (cell r2 c2)) N) target))

(define-fun cage-mod-3 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (target Int)) Bool
  (= (mod (+ (cell r1 c1) (cell r2 c2) (cell r3 c3)) N) target))

; ============================================================================
; SECTION 4: Killer Mode Constraints
; ============================================================================

; Killer cage constraint: no repeated digits within cage
(define-fun killer-2 ((r1 Int) (c1 Int) (r2 Int) (c2 Int)) Bool
  (not (= (cell r1 c1) (cell r2 c2))))

(define-fun killer-3 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int)) Bool
  (and (not (= (cell r1 c1) (cell r2 c2)))
       (not (= (cell r1 c1) (cell r3 c3)))
       (not (= (cell r2 c2) (cell r3 c3)))))

(define-fun killer-4 ((r1 Int) (c1 Int) (r2 Int) (c2 Int) (r3 Int) (c3 Int) (r4 Int) (c4 Int)) Bool
  (and (not (= (cell r1 c1) (cell r2 c2)))
       (not (= (cell r1 c1) (cell r3 c3)))
       (not (= (cell r1 c1) (cell r4 c4)))
       (not (= (cell r2 c2) (cell r3 c3)))
       (not (= (cell r2 c2) (cell r4 c4)))
       (not (= (cell r3 c3) (cell r4 c4)))))

; ============================================================================
; SECTION 5: Example 4x4 KenKen Puzzle
; ============================================================================

; Example cages for a 4x4 puzzle:
; ┌─────────┬─────────┐
; │  6+     │  2÷     │
; │(0,0)(0,1)(1,0)    (0,2)(0,3)
; ├─────────┼─────────┤
; │  8×     │  3-     │
; │(1,1)(1,2)(1,3)    (2,0)(3,0)
; ├─────────┼─────────┤
; │  5+     │  12×    │
; │(2,1)(2,2)(3,1)    (2,3)(3,2)(3,3)
; └─────────┴─────────┘

; Cage 1: cells (0,0), (0,1), (1,0) sum to 6
(assert (cage-add-3 0 0 0 1 1 0 6))

; Cage 2: cells (0,2), (0,3) divide to 2
(assert (cage-div-2 0 2 0 3 2))

; Cage 3: cells (1,1), (1,2), (1,3) multiply to 8
(assert (cage-mul-3 1 1 1 2 1 3 8))

; Cage 4: cells (2,0), (3,0) subtract to 3
(assert (cage-sub-2 2 0 3 0 3))

; Cage 5: cells (2,1), (2,2), (3,1) sum to 5
(assert (cage-add-3 2 1 2 2 3 1 5))

; Cage 6: cells (2,3), (3,2), (3,3) multiply to 12
(assert (cage-mul-3 2 3 3 2 3 3 12))

; ============================================================================
; SECTION 6: Solver Commands
; ============================================================================

(check-sat)
(get-model)

; ============================================================================
; SECTION 7: Programmatic Generation Interface
; ============================================================================

; The following functions are designed to be called programmatically
; from C code via Z3's C API (z3.h) or FFI bindings.

; grid_size: set the N parameter
; add_cell_value: assert (= (cell r c) v) for fixed cells
; add_cage: assert appropriate cage constraint based on operation

; Example fixed cell (given clue):
; (assert (= (cell 0 0) 1))

; ============================================================================
; SECTION 8: Uniqueness Check (for puzzle validation)
; ============================================================================

; To verify a puzzle has exactly one solution:
; 1. Find first solution with (check-sat) (get-model)
; 2. Add negation of solution: (assert (not (and (= (cell 0 0) v00) ...)))
; 3. Check again: if unsat, puzzle has unique solution

; ============================================================================
; SECTION 9: DLX-SAT Hybrid Threshold Decision
; ============================================================================

; The hybrid architecture uses DLX for exact cover (fast for small cages)
; and SAT/SMT for large cages where tuple enumeration exceeds threshold.
;
; Threshold heuristics (from HYBRID_DLX_SAT_ARCHITECTURE.md):
; - TUPLE_THRESHOLD_SMALL = 100   (force enumeration)
; - TUPLE_THRESHOLD_DLX = 500     (prefer DLX)
; - TUPLE_THRESHOLD_SAT = 1000    (switch to SAT)
; - TUPLE_THRESHOLD_ABORT = 2000  (retry with different cages)
;
; For a cage of size k with values 1..n, max tuples = n^k
; Examples:
; - 4-cell cage in 9x9: 9^4 = 6561 > 1000 → use SAT
; - 3-cell cage in 6x6: 6^3 = 216 < 500 → use DLX
; - 5-cell cage in 16x16: 16^5 = 1048576 → definitely SAT

; ============================================================================
; END OF SPECIFICATION
; ============================================================================
