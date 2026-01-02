; Latin Square 4x4 - Minimal SMT Encoding
; Author: KeenKenning Project
; SPDX-License-Identifier: MIT

(set-logic QF_LIA)

; Cell values: cell_r_c represents value at row r, column c (0-indexed)
(declare-const cell_0_0 Int) (declare-const cell_0_1 Int)
(declare-const cell_0_2 Int) (declare-const cell_0_3 Int)
(declare-const cell_1_0 Int) (declare-const cell_1_1 Int)
(declare-const cell_1_2 Int) (declare-const cell_1_3 Int)
(declare-const cell_2_0 Int) (declare-const cell_2_1 Int)
(declare-const cell_2_2 Int) (declare-const cell_2_3 Int)
(declare-const cell_3_0 Int) (declare-const cell_3_1 Int)
(declare-const cell_3_2 Int) (declare-const cell_3_3 Int)

; Value range: 1 to 4
(assert (and (>= cell_0_0 1) (<= cell_0_0 4)))
(assert (and (>= cell_0_1 1) (<= cell_0_1 4)))
(assert (and (>= cell_0_2 1) (<= cell_0_2 4)))
(assert (and (>= cell_0_3 1) (<= cell_0_3 4)))
(assert (and (>= cell_1_0 1) (<= cell_1_0 4)))
(assert (and (>= cell_1_1 1) (<= cell_1_1 4)))
(assert (and (>= cell_1_2 1) (<= cell_1_2 4)))
(assert (and (>= cell_1_3 1) (<= cell_1_3 4)))
(assert (and (>= cell_2_0 1) (<= cell_2_0 4)))
(assert (and (>= cell_2_1 1) (<= cell_2_1 4)))
(assert (and (>= cell_2_2 1) (<= cell_2_2 4)))
(assert (and (>= cell_2_3 1) (<= cell_2_3 4)))
(assert (and (>= cell_3_0 1) (<= cell_3_0 4)))
(assert (and (>= cell_3_1 1) (<= cell_3_1 4)))
(assert (and (>= cell_3_2 1) (<= cell_3_2 4)))
(assert (and (>= cell_3_3 1) (<= cell_3_3 4)))

; Row uniqueness
; Row 0
(assert (distinct cell_0_0 cell_0_1 cell_0_2 cell_0_3))
; Row 1
(assert (distinct cell_1_0 cell_1_1 cell_1_2 cell_1_3))
; Row 2
(assert (distinct cell_2_0 cell_2_1 cell_2_2 cell_2_3))
; Row 3
(assert (distinct cell_3_0 cell_3_1 cell_3_2 cell_3_3))

; Column uniqueness
; Col 0
(assert (distinct cell_0_0 cell_1_0 cell_2_0 cell_3_0))
; Col 1
(assert (distinct cell_0_1 cell_1_1 cell_2_1 cell_3_1))
; Col 2
(assert (distinct cell_0_2 cell_1_2 cell_2_2 cell_3_2))
; Col 3
(assert (distinct cell_0_3 cell_1_3 cell_2_3 cell_3_3))

; ============================================================================
; Example KenKen cages (simple valid puzzle)
; Grid layout:
; ┌───┬───┬───┬───┐
; │7+ │   │2÷ │   │
; │   │6× │   │   │
; ├───┼───┼───┼───┤
; │   │   │   │3- │
; │   │   │   │   │
; └───┴───┴───┴───┘
;
; Cage 1: (0,0)+(1,0) = 7  [2-cell vertical addition]
; Cage 2: (0,1)*(1,1) = 6  [2-cell vertical multiplication]
; Cage 3: (0,2)/(0,3) = 2  [2-cell horizontal division]
; Cage 4: (1,2)-(1,3) = 3  [2-cell horizontal subtraction]
; ============================================================================

; Cage 1: Addition cage = 7
(assert (= (+ cell_0_0 cell_1_0) 7))

; Cage 2: Multiplication cage = 6
(assert (= (* cell_0_1 cell_1_1) 6))

; Cage 3: Division cage = 2 (order-independent)
(assert (or (= (* cell_0_3 2) cell_0_2)
            (= (* cell_0_2 2) cell_0_3)))

; Cage 4: Subtraction cage = 3 (order-independent: |a-b| = 3)
(assert (or (= (- cell_1_2 cell_1_3) 3)
            (= (- cell_1_3 cell_1_2) 3)))

; Remaining cells need their own cages (single-cell cages)
; (2,0) = value, (2,1) = value, etc.
; For simplicity, leave remaining cells as free Latin square constraints

(check-sat)
(get-model)
