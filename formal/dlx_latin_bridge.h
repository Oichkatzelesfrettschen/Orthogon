/**
 * @file dlx_latin_bridge.h
 * @brief Integration bridge between verified Latin square matrix and DLX solver
 *
 * This header provides the API to solve Latin squares using:
 * 1. Formally verified constraint matrix generation (keen_verified.c)
 * 2. DLX exact cover solver (dlx.c)
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#ifndef DLX_LATIN_BRIDGE_H
#define DLX_LATIN_BRIDGE_H

#include "keen_verified.h"
#include "dlx.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Statistics from DLX Latin square solving
 */
typedef struct {
    int matrix_rows;    /**< Number of rows in constraint matrix (n^3) */
    int matrix_cols;    /**< Number of columns (3*n^2) */
    int matrix_ones;    /**< Total 1s in matrix (3*n^3) */
    int dlx_nodes;      /**< DLX nodes allocated */
    int solution_rows;  /**< Rows in solution (should be n^2) */
    bool verified;      /**< Solution passed kv_validate_latin */
    bool success;       /**< Overall success flag */
} dlx_latin_stats_t;

/**
 * @brief Solve Latin square using verified DLX
 *
 * This function:
 * 1. Builds the exact cover matrix using kv_build_latin_matrix() (verified)
 * 2. Converts to DLX format and solves using dlx_solve()
 * 3. Extracts and validates the solution using kv_validate_latin() (verified)
 *
 * The extraction path ensures correctness:
 *   Coq proof -> OCaml extraction -> C (kv_*) -> DLX -> verified solution
 *
 * @param n Grid dimension (1-16)
 * @param solution Output grid, n*n integers (1-indexed values)
 * @return true if solution found and verified
 */
bool kv_solve_latin_dlx(int n, int *solution);

/**
 * @brief Solve Latin square with statistics
 *
 * Same as kv_solve_latin_dlx but returns detailed statistics
 * about the constraint matrix and solving process.
 *
 * @param n Grid dimension (1-16)
 * @param solution Output grid, n*n integers (1-indexed values)
 * @return Statistics structure with success flag
 */
dlx_latin_stats_t kv_solve_latin_dlx_stats(int n, int *solution);

/**
 * @brief Print statistics to stdout
 *
 * @param stats Statistics from kv_solve_latin_dlx_stats
 * @param n Grid dimension (for display)
 */
void kv_print_latin_stats(const dlx_latin_stats_t *stats, int n);

#ifdef __cplusplus
}
#endif

#endif /* DLX_LATIN_BRIDGE_H */
