/**
 * @file latin_bounds.h
 * @brief Formally verified Latin square enumeration bounds
 *
 * This header provides compile-time constants and functions for Latin square
 * enumeration, extracted from Coq formal specification (formal/LatinEnum.v).
 *
 * Key mathematical facts proven in Coq:
 *   - There are exactly 12 Latin squares of order 3 (OEIS A002860)
 *   - There is exactly 1 reduced Latin square of order 3 (OEIS A000315)
 *   - L(n) = n! × (n-1)! × R(n) where L=total, R=reduced
 *   - 3x3 HARD+ requires constraint expansion due to small solution space
 *
 * @see formal/LatinEnum.v for Coq proofs
 * @see formal/Modes.v for mode flag specifications
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 */

#ifndef LATIN_BOUNDS_H
#define LATIN_BOUNDS_H

#include <stdint.h>

/**
 * @defgroup OEIS_A002860 Latin Square Counts
 * Number of Latin squares of order n (OEIS A002860)
 * @{
 */
#define LATIN_COUNT_1 1U
#define LATIN_COUNT_2 2U
#define LATIN_COUNT_3 12U
#define LATIN_COUNT_4 576U
#define LATIN_COUNT_5 161280U
#define LATIN_COUNT_6 812851200U
/** @} */

/**
 * @defgroup OEIS_A000315 Reduced Latin Square Counts
 * Number of reduced Latin squares of order n (OEIS A000315)
 * @{
 */
#define REDUCED_COUNT_1 1U
#define REDUCED_COUNT_2 1U
#define REDUCED_COUNT_3 1U
#define REDUCED_COUNT_4 4U
#define REDUCED_COUNT_5 56U
#define REDUCED_COUNT_6 9408U
/** @} */

/**
 * @defgroup MODE_FLAGS Mode Flags (from keen_modes.h)
 * These must match the values in keen_modes.h and GameMode.kt
 * @{
 */
#define LATIN_MODE_KILLER  0x40U   /* 64: No repeated digits in cages */
#define LATIN_MODE_BITWISE 0x800U  /* 2048: XOR operations */
#define LATIN_MODE_MODULAR 0x20U   /* 32: Wrap-around arithmetic */
/** @} */

/**
 * @defgroup DIFFICULTY_LEVELS Difficulty Thresholds
 * @{
 */
#define DIFF_EASY 0
#define DIFF_NORMAL 1
#define DIFF_HARD 2
#define DIFF_EXTREME 3
#define DIFF_UNREASONABLE 4
/** @} */

/**
 * Get number of Latin squares for grid size n.
 *
 * @param n Grid size (1-6 for exact values, 0 for larger)
 * @return Number of Latin squares, or 0 if unknown
 *
 * Proven in Coq: latin_3x3_count : latin_count 3 = 12.
 */
[[nodiscard]]
static inline uint32_t latin_count(unsigned int n) {
    static const uint32_t counts[] = {
        0,          /* n=0: undefined */
        LATIN_COUNT_1,
        LATIN_COUNT_2,
        LATIN_COUNT_3,
        LATIN_COUNT_4,
        LATIN_COUNT_5,
        LATIN_COUNT_6
    };
    return (n <= 6) ? counts[n] : 0;
}

/**
 * Get number of reduced Latin squares for grid size n.
 *
 * @param n Grid size (1-6 for exact values, 0 for larger)
 * @return Number of reduced Latin squares, or 0 if unknown
 *
 * Proven in Coq: reduced_3x3_count : reduced_count 3 = 1.
 */
[[nodiscard]]
static inline uint32_t reduced_count(unsigned int n) {
    static const uint32_t counts[] = {
        0,          /* n=0: undefined */
        REDUCED_COUNT_1,
        REDUCED_COUNT_2,
        REDUCED_COUNT_3,
        REDUCED_COUNT_4,
        REDUCED_COUNT_5,
        REDUCED_COUNT_6
    };
    return (n <= 6) ? counts[n] : 0;
}

/**
 * Compute factorial for small n.
 *
 * @param n Value (0-12 for safe uint32_t results)
 * @return n! or 0 on overflow
 */
[[nodiscard]]
static inline uint32_t factorial(unsigned int n) {
    static const uint32_t facts[] = {
        1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600
    };
    return (n <= 12) ? facts[n] : 0;
}

/**
 * Compute mode upgrade flags for 3x3 HARD+ difficulties.
 *
 * Mathematical justification (proven in Coq):
 *   - 3x3 has only 12 Latin squares (small solution space)
 *   - HARD+ difficulty requires constraint expansion
 *   - Adding KILLER/BITWISE/MODULAR modes increases ambiguity
 *
 * @param grid_size Grid dimension (3 triggers upgrade)
 * @param difficulty Difficulty level (0=Easy, 2=Hard, 3=Extreme, 4+=Unreasonable)
 * @return Mode flags to OR with base mode, or 0 if no upgrade needed
 *
 * Proven in Coq:
 *   - auto_upgrade_3x3_hard_adds_killer : auto_upgrade_modes 3 2 = MODE_KILLER
 *   - auto_upgrade_3x3_extreme_adds_bitwise : auto_upgrade_modes 3 3 = MODE_KILLER + MODE_BITWISE
 */
[[nodiscard]]
static inline unsigned int auto_upgrade_modes(unsigned int grid_size, unsigned int difficulty) {
    if (grid_size != 3) {
        return 0;  /* Only 3x3 needs upgrade */
    }

    if (difficulty < DIFF_HARD) {
        return 0;  /* Easy/Normal don't need upgrade */
    }

    if (difficulty == DIFF_HARD) {
        return LATIN_MODE_KILLER;
    }

    if (difficulty == DIFF_EXTREME) {
        return LATIN_MODE_KILLER | LATIN_MODE_BITWISE;
    }

    /* Unreasonable+ */
    return LATIN_MODE_KILLER | LATIN_MODE_BITWISE | LATIN_MODE_MODULAR;
}

/**
 * Check if solution space is sufficient for difficulty without mode upgrade.
 *
 * @param grid_size Grid dimension
 * @return true if >= 100 Latin squares exist
 *
 * Proven in Coq: small_3x3_solution_space : solution_space 3 = 12.
 */
[[nodiscard]]
static inline bool solution_space_sufficient(unsigned int grid_size) {
    return latin_count(grid_size) >= 100;
}

#endif /* LATIN_BOUNDS_H */
