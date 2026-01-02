/**
 * @file keen_verified.h
 * @brief Verified Latin square and exact cover algorithms
 *
 * This header provides C implementations derived from formally verified
 * Coq specifications. The algorithms have been proven correct for:
 * - Latin square constraint generation
 * - Exact cover checking
 * - CNF clause generation for SAT solving
 *
 * Extraction path: Coq -> OCaml -> C
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#ifndef KEEN_VERIFIED_H
#define KEEN_VERIFIED_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * Type Definitions (from Coq extraction)
 * ============================================================================ */

/** A row in the exact cover matrix (list of column indices) */
typedef struct {
    int *cols;      /**< Column indices */
    int count;      /**< Number of columns */
} kv_row_t;

/** Exact cover matrix */
typedef struct {
    kv_row_t *rows; /**< Array of rows */
    int num_rows;   /**< Number of rows */
    int num_cols;   /**< Number of columns */
} kv_matrix_t;

/** Solution: list of row indices */
typedef struct {
    int *indices;   /**< Row indices in solution */
    int count;      /**< Number of rows */
} kv_solution_t;

/** CNF clause (disjunction of literals) */
typedef struct {
    int *literals;  /**< Literals (positive=true, negative=negated) */
    int count;      /**< Number of literals */
} kv_clause_t;

/** CNF formula (conjunction of clauses) */
typedef struct {
    kv_clause_t *clauses; /**< Array of clauses */
    int count;            /**< Number of clauses */
    int max_var;          /**< Maximum variable number */
} kv_cnf_t;

/* ============================================================================
 * Exact Cover Functions (from DLX.v)
 * ============================================================================ */

/**
 * @brief Check if a list has duplicate elements
 *
 * Verified property: Returns true iff some element appears twice.
 *
 * @param arr Array of integers
 * @param len Length of array
 * @return true if duplicates exist
 */
bool kv_has_duplicates(const int *arr, int len);

/**
 * @brief Get columns covered by selected rows
 *
 * @param matrix The exact cover matrix
 * @param solution Row indices to check
 * @param out_cols Output array (must be large enough)
 * @param out_count Output: number of columns
 */
void kv_covered_cols(const kv_matrix_t *matrix,
                     const kv_solution_t *solution,
                     int *out_cols,
                     int *out_count);

/**
 * @brief Check if solution is an exact cover
 *
 * Verified property: Returns true iff solution covers each column exactly once.
 *
 * @param matrix The exact cover matrix
 * @param solution Proposed solution
 * @return true if exact cover
 */
bool kv_is_exact_cover(const kv_matrix_t *matrix, const kv_solution_t *solution);

/**
 * @brief Build Latin square exact cover matrix
 *
 * Creates matrix with:
 * - N^3 rows (each placement (r,c,v))
 * - 3N^2 columns (cell-filled, row-has-value, col-has-value)
 *
 * @param n Grid dimension
 * @param matrix Output matrix (caller must free)
 * @return true on success
 */
bool kv_build_latin_matrix(int n, kv_matrix_t *matrix);

/**
 * @brief Free matrix resources
 */
void kv_free_matrix(kv_matrix_t *matrix);

/* ============================================================================
 * SAT Encoding Functions (from SAT.v)
 * ============================================================================ */

/**
 * @brief Variable number for cell(r,c)=d
 *
 * Encoding: r*n*n + c*n + d + 1 (1-indexed for DIMACS)
 *
 * @param n Grid dimension
 * @param r Row (0-indexed)
 * @param c Column (0-indexed)
 * @param d Digit (0-indexed, so 0 means value 1)
 * @return Variable number
 */
static inline int kv_var_cell_digit(int n, int r, int c, int d) {
    return r * n * n + c * n + d + 1;
}

/**
 * @brief Generate Latin square CNF
 *
 * Creates clauses for:
 * - Each cell has exactly one digit
 * - Each row has each digit exactly once
 * - Each column has each digit exactly once
 *
 * @param n Grid dimension
 * @param cnf Output CNF (caller must free)
 * @return true on success
 */
bool kv_latin_cnf(int n, kv_cnf_t *cnf);

/**
 * @brief Add cage constraint clauses
 *
 * @param n Grid dimension
 * @param cells Cell positions (row*n + col for each cell)
 * @param num_cells Number of cells in cage
 * @param op Operation (0=add, 1=sub, 2=mul, 3=div, 4=xor, 5=mod)
 * @param target Target value
 * @param killer If true, add no-repeat constraint
 * @param cnf CNF to append to
 * @return true on success
 */
bool kv_add_cage_cnf(int n,
                     const int *cells,
                     int num_cells,
                     int op,
                     int target,
                     bool killer,
                     kv_cnf_t *cnf);

/**
 * @brief Free CNF resources
 */
void kv_free_cnf(kv_cnf_t *cnf);

/**
 * @brief Write CNF in DIMACS format
 *
 * @param cnf The CNF formula
 * @param out Output file
 * @return Number of clauses written, or -1 on error
 */
int kv_write_dimacs(const kv_cnf_t *cnf, void *out /* FILE* */);

/* ============================================================================
 * Integration with DLX
 * ============================================================================ */

/**
 * @brief Solve Latin square using DLX
 *
 * Uses the existing dlx.c implementation with verified matrix construction.
 *
 * @param n Grid dimension
 * @param solution Output grid (n*n values, 1-indexed)
 * @return true on success
 */
bool kv_solve_latin_dlx(int n, int *solution);

/**
 * @brief Check solution against verified properties
 *
 * Validates that solution satisfies all Latin square constraints.
 *
 * @param n Grid dimension
 * @param grid Grid values (n*n, 1-indexed)
 * @return true if valid Latin square
 */
bool kv_validate_latin(int n, const int *grid);

#ifdef __cplusplus
}
#endif

#endif /* KEEN_VERIFIED_H */
