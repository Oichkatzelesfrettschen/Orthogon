/**
 * @file latin_verified.c
 * @brief Implementation of verified Latin square generation
 *
 * Wraps the Coq-extracted DLX solver for use as a drop-in replacement
 * for latin_generate() in puzzle generation.
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#define _POSIX_C_SOURCE 199309L  /* For clock_gettime */

#include "latin_verified.h"
#include "dlx_latin_bridge.h"
#include "keen_verified.h"

#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Thread-local statistics from last generation */
static _Thread_local int last_matrix_rows = 0;
static _Thread_local int last_matrix_cols = 0;
static _Thread_local long last_solve_time_us = 0;
static _Thread_local bool stats_valid = false;

/**
 * @brief Get current time in microseconds
 */
static long get_time_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000000L + ts.tv_nsec / 1000L;
}

unsigned char *latin_generate_verified(int n) {
    /* Validate input */
    if (n < 2 || n > 16) {
        stats_valid = false;
        return NULL;
    }

    /* Allocate solution grid */
    int *int_solution = malloc((size_t)n * (size_t)n * sizeof(int));
    if (!int_solution) {
        stats_valid = false;
        return NULL;
    }

    /* Time the solve */
    long start_time = get_time_us();

    /* Solve using verified DLX */
    dlx_latin_stats_t stats = kv_solve_latin_dlx_stats(n, int_solution);

    long end_time = get_time_us();

    /* Store statistics */
    last_matrix_rows = stats.matrix_rows;
    last_matrix_cols = stats.matrix_cols;
    last_solve_time_us = end_time - start_time;
    stats_valid = true;

    if (!stats.success || !stats.verified) {
        free(int_solution);
        return NULL;
    }

    /* Convert to unsigned char (digit type) for latin.h compatibility */
    unsigned char *sq = malloc((size_t)n * (size_t)n * sizeof(unsigned char));
    if (!sq) {
        free(int_solution);
        return NULL;
    }

    for (int i = 0; i < n * n; i++) {
        sq[i] = (unsigned char)int_solution[i];
    }

    free(int_solution);
    return sq;
}

unsigned char *latin_generate_verified_shuffled(int n, unsigned int seed) {
    /* Generate base square */
    unsigned char *sq = latin_generate_verified(n);
    if (!sq) {
        return NULL;
    }

    /* Initialize random seed */
    if (seed == 0) {
        seed = (unsigned int)time(NULL);
    }
    srand(seed);

    /* Generate random permutations for rows, columns, and symbols */
    int *row_perm = malloc((size_t)n * sizeof(int));
    int *col_perm = malloc((size_t)n * sizeof(int));
    int *sym_perm = malloc((size_t)n * sizeof(int));
    unsigned char *shuffled = malloc((size_t)n * (size_t)n * sizeof(unsigned char));

    if (!row_perm || !col_perm || !sym_perm || !shuffled) {
        free(row_perm);
        free(col_perm);
        free(sym_perm);
        free(shuffled);
        free(sq);
        return NULL;
    }

    /* Initialize permutations as identity */
    for (int i = 0; i < n; i++) {
        row_perm[i] = i;
        col_perm[i] = i;
        sym_perm[i] = i;
    }

    /* Fisher-Yates shuffle for each permutation */
    for (int i = n - 1; i > 0; i--) {
        int j = rand() % (i + 1);
        int tmp = row_perm[i];
        row_perm[i] = row_perm[j];
        row_perm[j] = tmp;

        j = rand() % (i + 1);
        tmp = col_perm[i];
        col_perm[i] = col_perm[j];
        col_perm[j] = tmp;

        j = rand() % (i + 1);
        tmp = sym_perm[i];
        sym_perm[i] = sym_perm[j];
        sym_perm[j] = tmp;
    }

    /* Apply permutations: shuffled[row_perm[r]][col_perm[c]] = sym_perm[sq[r][c] - 1] + 1 */
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < n; c++) {
            int old_val = sq[r * n + c] - 1;  /* 0-indexed symbol */
            int new_val = sym_perm[old_val] + 1;  /* 1-indexed result */
            int new_r = row_perm[r];
            int new_c = col_perm[c];
            shuffled[new_r * n + new_c] = (unsigned char)new_val;
        }
    }

    free(row_perm);
    free(col_perm);
    free(sym_perm);
    free(sq);

    return shuffled;
}

void latin_verified_free(unsigned char *sq) {
    free(sq);
}

bool latin_check_verified(const unsigned char *sq, int n) {
    if (!sq || n < 1 || n > 16) {
        return false;
    }

    /* Convert to int array for kv_validate_latin */
    int *grid = malloc((size_t)n * (size_t)n * sizeof(int));
    if (!grid) {
        return false;
    }

    for (int i = 0; i < n * n; i++) {
        grid[i] = sq[i];
    }

    bool valid = kv_validate_latin(n, grid);

    free(grid);
    return valid;
}

bool latin_verified_get_stats(int *out_matrix_rows, int *out_matrix_cols,
                              long *out_solve_time_us) {
    if (!stats_valid) {
        return false;
    }

    if (out_matrix_rows) *out_matrix_rows = last_matrix_rows;
    if (out_matrix_cols) *out_matrix_cols = last_matrix_cols;
    if (out_solve_time_us) *out_solve_time_us = last_solve_time_us;

    return true;
}
