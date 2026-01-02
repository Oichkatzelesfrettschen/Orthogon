/**
 * @file latin_verified.h
 * @brief Verified Latin square generation using Coq-extracted DLX solver
 *
 * This header provides latin_generate_verified(), a formally verified
 * alternative to latin_generate() that uses the Coq-proven DLX algorithm.
 *
 * The function signature matches latin.h conventions for drop-in replacement.
 *
 * Verification chain:
 *   Coq proof (LatinSquare.v) -> OCaml extraction -> C translation
 *   -> DLX solving (dlx.c) -> Coq-validated result (kv_validate_latin)
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#ifndef LATIN_VERIFIED_H
#define LATIN_VERIFIED_H

#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Generate a Latin square using verified DLX algorithm
 *
 * This function generates a valid Latin square of order n using
 * the formally verified constraint matrix construction and DLX solver.
 *
 * Unlike latin_generate(), this function:
 * - Does not require random_state (deterministic)
 * - Always produces the lexicographically first solution
 * - Is formally verified for correctness
 *
 * @param n Grid dimension (2-16)
 * @return Newly allocated array of n*n digits (1-indexed values), or NULL on failure
 *         Caller must free with sfree() or latin_verified_free()
 *
 * @note Values are 1-indexed (1..n) to match latin_generate() output
 * @note Returns NULL for n < 2 or n > 16
 */
unsigned char *latin_generate_verified(int n);

/**
 * @brief Generate with shuffled rows/columns for variety
 *
 * Generates a verified Latin square, then applies a random permutation
 * of rows, columns, and symbols to add variety while preserving validity.
 *
 * @param n Grid dimension (2-16)
 * @param seed Random seed for permutations (0 = use time)
 * @return Newly allocated shuffled Latin square, or NULL on failure
 */
unsigned char *latin_generate_verified_shuffled(int n, unsigned int seed);

/**
 * @brief Free memory allocated by latin_generate_verified
 *
 * @param sq Square returned by latin_generate_verified functions
 */
void latin_verified_free(unsigned char *sq);

/**
 * @brief Check if a grid is a valid Latin square (verified check)
 *
 * Uses the Coq-extracted validation function kv_validate_latin.
 *
 * @param sq Grid to check (n*n values, 1-indexed)
 * @param n Grid dimension
 * @return true if valid Latin square, false otherwise
 */
bool latin_check_verified(const unsigned char *sq, int n);

/**
 * @brief Get statistics from the last generation
 *
 * @param out_matrix_rows Output: rows in constraint matrix (n^3)
 * @param out_matrix_cols Output: columns in constraint matrix (3n^2)
 * @param out_solve_time_us Output: solve time in microseconds
 * @return true if statistics available, false if no generation performed
 */
bool latin_verified_get_stats(int *out_matrix_rows, int *out_matrix_cols,
                              long *out_solve_time_us);

#ifdef __cplusplus
}
#endif

#endif /* LATIN_VERIFIED_H */
