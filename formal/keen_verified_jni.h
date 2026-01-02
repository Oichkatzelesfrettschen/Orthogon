/**
 * @file keen_verified_jni.h
 * @brief JNI-compatible interface for verified Latin square generation
 *
 * This header provides a clean C interface for integrating the Coq-verified
 * Latin square solver into the Android app via JNI. It wraps the formal
 * verification pipeline:
 *
 *   Java -> JNI -> keen_verified_jni -> latin_verified -> DLX solver
 *
 * The functions here are designed to be easily callable from keen-android-jni.c
 * and can replace or augment the existing latin_generate() calls.
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#ifndef KEEN_VERIFIED_JNI_H
#define KEEN_VERIFIED_JNI_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Result structure for verified generation
 *
 * This structure packages the result of Latin square generation
 * in a format suitable for JNI marshaling.
 */
typedef struct {
    bool success;           /**< True if generation succeeded */
    bool verified;          /**< True if result passed Coq-verified validation */
    int grid_size;          /**< Grid dimension (n) */
    int solve_time_ms;      /**< Time to solve in milliseconds */
    int matrix_rows;        /**< Constraint matrix rows (n^3) */
    int matrix_cols;        /**< Constraint matrix columns (3n^2) */
} kv_jni_stats_t;

/**
 * @brief Generate a verified Latin square for JNI
 *
 * This is the main entry point for Android integration. It generates
 * a valid Latin square using the formally verified DLX algorithm,
 * with optional shuffling for variety.
 *
 * Memory management:
 * - The returned grid is allocated with malloc() and must be freed
 *   by the caller using kv_jni_free_grid()
 * - Grid values are 1-indexed (1..n), matching latin_generate()
 *
 * @param n Grid dimension (2-16)
 * @param shuffle If true, apply random permutations for variety
 * @param seed Random seed for shuffling (0 = use time)
 * @param out_stats Optional statistics output (may be NULL)
 * @return Newly allocated grid (n*n int8_t values), or NULL on failure
 *
 * Example usage in keen-android-jni.c:
 * @code
 * kv_jni_stats_t stats;
 * int8_t *grid = kv_jni_generate_latin(9, true, 0, &stats);
 * if (grid && stats.verified) {
 *     // Use verified grid for puzzle generation
 *     for (int i = 0; i < 81; i++) {
 *         solution[i] = grid[i];  // Already 1-indexed
 *     }
 * }
 * kv_jni_free_grid(grid);
 * @endcode
 */
int8_t *kv_jni_generate_latin(int n, bool shuffle, uint32_t seed,
                               kv_jni_stats_t *out_stats);

/**
 * @brief Free a grid allocated by kv_jni_generate_latin
 *
 * @param grid Grid to free (safe to call with NULL)
 */
void kv_jni_free_grid(int8_t *grid);

/**
 * @brief Validate a Latin square using verified validation
 *
 * Uses the Coq-extracted validation function to check if a grid
 * is a valid Latin square.
 *
 * @param grid Grid to validate (n*n values, 1-indexed)
 * @param n Grid dimension
 * @return true if valid Latin square, false otherwise
 */
bool kv_jni_validate_latin(const int8_t *grid, int n);

/**
 * @brief Check if verified solver is available
 *
 * This function can be used to determine at runtime whether
 * the verified solver is linked and functional.
 *
 * @return true if verified solver available
 */
bool kv_jni_is_available(void);

/**
 * @brief Get version string for the verified solver
 *
 * Returns a string like "KeenKenning Verified Solver v1.0 (Coq-extracted)"
 *
 * @return Static version string (do not free)
 */
const char *kv_jni_version(void);

/**
 * @brief Maximum supported grid size
 */
#define KV_JNI_MAX_SIZE 16

/**
 * @brief Minimum supported grid size
 */
#define KV_JNI_MIN_SIZE 2

#ifdef __cplusplus
}
#endif

#endif /* KEEN_VERIFIED_JNI_H */
