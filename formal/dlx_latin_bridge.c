/**
 * @file dlx_latin_bridge.c
 * @brief Integration bridge between verified Latin square matrix and DLX solver
 *
 * This module connects the formally verified constraint matrix generation
 * (keen_verified.c) with the DLX solver implementation (dlx.c).
 *
 * Extraction path: Coq -> OCaml -> C (keen_verified.c) -> DLX (dlx.c)
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#include "dlx_latin_bridge.h"
#include <string.h>
#include <stdio.h>

/* ============================================================================
 * Matrix Format Conversion
 * ============================================================================ */

/**
 * @brief Convert kv_matrix_t to int** format for dlx_new()
 *
 * The DLX solver expects a dense row-major matrix where matrix[r][c] = 1
 * if row r covers column c. The verified kv_matrix_t uses sparse rows.
 *
 * @param kv_matrix Source verified matrix
 * @param out_matrix Output dense matrix (allocated by caller)
 * @return true on success
 */
static bool kv_to_dense_matrix(const kv_matrix_t *kv_matrix, int **out_matrix) {
    if (!kv_matrix || !out_matrix) return false;

    /* Initialize all entries to 0 */
    for (int r = 0; r < kv_matrix->num_rows; r++) {
        memset(out_matrix[r], 0, (size_t)kv_matrix->num_cols * sizeof(int));
    }

    /* Set 1s according to sparse representation */
    for (int r = 0; r < kv_matrix->num_rows; r++) {
        const kv_row_t *row = &kv_matrix->rows[r];
        for (int j = 0; j < row->count; j++) {
            int col = row->cols[j];
            if (col >= 0 && col < kv_matrix->num_cols) {
                out_matrix[r][col] = 1;
            }
        }
    }

    return true;
}

/**
 * @brief Allocate dense matrix for DLX
 */
static int **alloc_dense_matrix(int rows, int cols) {
    int **matrix = (int **)malloc((size_t)rows * sizeof(int *));
    if (!matrix) return NULL;

    for (int i = 0; i < rows; i++) {
        matrix[i] = (int *)calloc((size_t)cols, sizeof(int));
        if (!matrix[i]) {
            /* Cleanup on failure */
            for (int j = 0; j < i; j++) {
                free(matrix[j]);
            }
            free(matrix);
            return NULL;
        }
    }

    return matrix;
}

/**
 * @brief Free dense matrix
 */
static void free_dense_matrix(int **matrix, int rows) {
    if (!matrix) return;
    for (int i = 0; i < rows; i++) {
        free(matrix[i]);
    }
    free(matrix);
}

/* ============================================================================
 * Solution Extraction
 * ============================================================================ */

/**
 * @brief Extract Latin square solution from DLX row indices
 *
 * Each DLX row represents a placement (r, c, v) where:
 *   row_index = r * n * n + c * n + v
 *
 * @param n Grid size
 * @param sol_rows DLX solution row indices
 * @param sol_size Number of rows in solution
 * @param grid Output grid (n*n values, 1-indexed)
 * @return true on success
 */
static bool extract_solution(int n, const int *sol_rows, int sol_size, int *grid) {
    if (!sol_rows || !grid || sol_size != n * n) {
        return false;
    }

    /* Initialize grid to 0 */
    memset(grid, 0, (size_t)(n * n) * sizeof(int));

    /* Decode each row index */
    for (int i = 0; i < sol_size; i++) {
        int row_idx = sol_rows[i];

        /* Decode: row_idx = r * n * n + c * n + v */
        int r = row_idx / (n * n);
        int rem = row_idx % (n * n);
        int c = rem / n;
        int v = rem % n;

        /* Validate bounds */
        if (r < 0 || r >= n || c < 0 || c >= n || v < 0 || v >= n) {
            return false;
        }

        /* Store value (1-indexed) */
        grid[r * n + c] = v + 1;
    }

    return true;
}

/* ============================================================================
 * Public API
 * ============================================================================ */

bool kv_solve_latin_dlx(int n, int *solution) {
    if (n <= 0 || n > 16 || !solution) {
        return false;
    }

    /* Step 1: Build verified constraint matrix */
    kv_matrix_t kv_matrix;
    if (!kv_build_latin_matrix(n, &kv_matrix)) {
        return false;
    }

    /* Step 2: Convert to dense matrix for DLX */
    int **dense = alloc_dense_matrix(kv_matrix.num_rows, kv_matrix.num_cols);
    if (!dense) {
        kv_free_matrix(&kv_matrix);
        return false;
    }

    if (!kv_to_dense_matrix(&kv_matrix, dense)) {
        free_dense_matrix(dense, kv_matrix.num_rows);
        kv_free_matrix(&kv_matrix);
        return false;
    }

    /* Step 3: Create DLX context and solve */
    dlx_ctx *ctx = dlx_new(kv_matrix.num_rows, kv_matrix.num_cols, dense);
    if (!ctx) {
        free_dense_matrix(dense, kv_matrix.num_rows);
        kv_free_matrix(&kv_matrix);
        return false;
    }

    int found = dlx_solve(ctx);

    bool success = false;
    if (found) {
        int sol_size = 0;
        int *sol_rows = dlx_get_solution(ctx, &sol_size);

        if (sol_rows && sol_size == n * n) {
            success = extract_solution(n, sol_rows, sol_size, solution);

            /* Verify solution with our verified checker */
            if (success && !kv_validate_latin(n, solution)) {
                success = false; /* Solution failed verification */
            }
        }
    }

    /* Cleanup */
    dlx_destroy(ctx);
    free_dense_matrix(dense, kv_matrix.num_rows);
    kv_free_matrix(&kv_matrix);

    return success;
}

dlx_latin_stats_t kv_solve_latin_dlx_stats(int n, int *solution) {
    dlx_latin_stats_t stats = {0};

    if (n <= 0 || n > 16 || !solution) {
        stats.success = false;
        return stats;
    }

    /* Build matrix and record stats */
    kv_matrix_t kv_matrix;
    if (!kv_build_latin_matrix(n, &kv_matrix)) {
        stats.success = false;
        return stats;
    }

    stats.matrix_rows = kv_matrix.num_rows;
    stats.matrix_cols = kv_matrix.num_cols;

    /* Count total ones in matrix */
    int total_ones = 0;
    for (int r = 0; r < kv_matrix.num_rows; r++) {
        total_ones += kv_matrix.rows[r].count;
    }
    stats.matrix_ones = total_ones;

    /* Convert and solve */
    int **dense = alloc_dense_matrix(kv_matrix.num_rows, kv_matrix.num_cols);
    if (!dense) {
        kv_free_matrix(&kv_matrix);
        stats.success = false;
        return stats;
    }

    kv_to_dense_matrix(&kv_matrix, dense);

    dlx_ctx *ctx = dlx_new(kv_matrix.num_rows, kv_matrix.num_cols, dense);
    if (!ctx) {
        free_dense_matrix(dense, kv_matrix.num_rows);
        kv_free_matrix(&kv_matrix);
        stats.success = false;
        return stats;
    }

    stats.dlx_nodes = ctx->n_nodes;

    int found = dlx_solve(ctx);

    if (found) {
        int sol_size = 0;
        int *sol_rows = dlx_get_solution(ctx, &sol_size);
        stats.solution_rows = sol_size;

        if (sol_rows && extract_solution(n, sol_rows, sol_size, solution)) {
            stats.verified = kv_validate_latin(n, solution);
            stats.success = stats.verified;
        }
    }

    dlx_destroy(ctx);
    free_dense_matrix(dense, kv_matrix.num_rows);
    kv_free_matrix(&kv_matrix);

    return stats;
}

void kv_print_latin_stats(const dlx_latin_stats_t *stats, int n) {
    if (!stats) return;

    printf("=== DLX Latin Square Statistics (n=%d) ===\n", n);
    printf("Matrix: %d rows x %d cols = %d constraints\n",
           stats->matrix_rows, stats->matrix_cols,
           stats->matrix_rows * stats->matrix_cols);
    printf("Matrix density: %d ones (%.2f%%)\n",
           stats->matrix_ones,
           100.0 * (double)stats->matrix_ones /
           ((double)stats->matrix_rows * (double)stats->matrix_cols));
    printf("DLX nodes allocated: %d\n", stats->dlx_nodes);
    printf("Solution rows: %d (expected: %d)\n", stats->solution_rows, n * n);
    printf("Verified: %s\n", stats->verified ? "YES" : "NO");
    printf("Success: %s\n", stats->success ? "YES" : "NO");
}
