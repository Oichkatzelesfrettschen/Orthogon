/**
 * @file keen_verified.c
 * @brief Verified Latin square and exact cover algorithms - C implementation
 *
 * This implementation is derived from formally verified Coq specifications.
 * The extraction path is: Coq -> OCaml -> C (manual translation).
 *
 * Key verified properties:
 * 1. kv_is_exact_cover correctly identifies exact covers
 * 2. kv_build_latin_matrix generates correct constraint matrix
 * 3. kv_latin_cnf generates satisfiable CNF for valid Latin squares
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#include "keen_verified.h"
#include <string.h>
#include <stdio.h>

/* ============================================================================
 * Helper Functions
 * ============================================================================ */

/**
 * @brief Binary search in sorted array
 */
[[maybe_unused]]
static bool binary_search(const int *arr, int len, int val) {
    int lo = 0, hi = len - 1;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        if (arr[mid] == val) return true;
        if (arr[mid] < val) lo = mid + 1;
        else hi = mid - 1;
    }
    return false;
}

/**
 * @brief Comparison for qsort
 */
static int int_compare(const void *a, const void *b) {
    return *(const int *)a - *(const int *)b;
}

/* ============================================================================
 * Exact Cover Functions (from DLX.v extraction)
 * ============================================================================ */

bool kv_has_duplicates(const int *arr, int len) {
    if (len <= 1) return false;

    /* O(n log n) approach: sort a copy and check adjacent */
    int *sorted = (int *)malloc((size_t)len * sizeof(int));
    if (!sorted) return false;

    memcpy(sorted, arr, (size_t)len * sizeof(int));
    qsort(sorted, (size_t)len, sizeof(int), int_compare);

    for (int i = 0; i < len - 1; i++) {
        if (sorted[i] == sorted[i + 1]) {
            free(sorted);
            return true;
        }
    }

    free(sorted);
    return false;
}

void kv_covered_cols(const kv_matrix_t *matrix,
                     const kv_solution_t *solution,
                     int *out_cols,
                     int *out_count) {
    int total = 0;

    for (int i = 0; i < solution->count; i++) {
        int row_idx = solution->indices[i];
        if (row_idx < 0 || row_idx >= matrix->num_rows) continue;

        const kv_row_t *row = &matrix->rows[row_idx];
        for (int j = 0; j < row->count; j++) {
            out_cols[total++] = row->cols[j];
        }
    }

    *out_count = total;
}

bool kv_is_exact_cover(const kv_matrix_t *matrix, const kv_solution_t *solution) {
    /* Allocate space for covered columns (max = all columns) */
    int *cols = (int *)malloc((size_t)matrix->num_cols * sizeof(int));
    if (!cols) return false;

    int count = 0;
    kv_covered_cols(matrix, solution, cols, &count);

    /* Check 1: No duplicates */
    if (kv_has_duplicates(cols, count)) {
        free(cols);
        return false;
    }

    /* Check 2: All columns covered */
    if (count != matrix->num_cols) {
        free(cols);
        return false;
    }

    /* Check 3: All row indices valid */
    for (int i = 0; i < solution->count; i++) {
        if (solution->indices[i] < 0 ||
            solution->indices[i] >= matrix->num_rows) {
            free(cols);
            return false;
        }
    }

    free(cols);
    return true;
}

bool kv_build_latin_matrix(int n, kv_matrix_t *matrix) {
    if (n <= 0) return false;

    /* Matrix dimensions:
     * - Rows: n^3 (each (r,c,v) placement)
     * - Columns: 3*n^2
     *   - 0..n^2-1: cell (r,c) is filled
     *   - n^2..2*n^2-1: row r has value v
     *   - 2*n^2..3*n^2-1: column c has value v
     */
    int num_rows = n * n * n;
    int num_cols = 3 * n * n;

    matrix->rows = (kv_row_t *)calloc((size_t)num_rows, sizeof(kv_row_t));
    if (!matrix->rows) return false;

    matrix->num_rows = num_rows;
    matrix->num_cols = num_cols;

    /* Generate rows */
    int row_idx = 0;
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < n; c++) {
            for (int v = 0; v < n; v++) {
                /* Allocate 3 columns per row */
                matrix->rows[row_idx].cols = (int *)malloc(3 * sizeof(int));
                if (!matrix->rows[row_idx].cols) {
                    kv_free_matrix(matrix);
                    return false;
                }
                matrix->rows[row_idx].count = 3;

                /* Column 0: cell (r,c) is filled */
                matrix->rows[row_idx].cols[0] = r * n + c;

                /* Column 1: row r has value v */
                matrix->rows[row_idx].cols[1] = n * n + r * n + v;

                /* Column 2: column c has value v */
                matrix->rows[row_idx].cols[2] = 2 * n * n + c * n + v;

                row_idx++;
            }
        }
    }

    return true;
}

void kv_free_matrix(kv_matrix_t *matrix) {
    if (!matrix) return;

    if (matrix->rows) {
        for (int i = 0; i < matrix->num_rows; i++) {
            free(matrix->rows[i].cols);
        }
        free(matrix->rows);
    }

    matrix->rows = NULL;
    matrix->num_rows = 0;
    matrix->num_cols = 0;
}

/* ============================================================================
 * SAT Encoding Functions (from SAT.v extraction)
 * ============================================================================ */

/**
 * @brief Add a clause to CNF (helper)
 */
static bool cnf_add_clause(kv_cnf_t *cnf, const int *lits, int count) {
    /* Grow array if needed */
    kv_clause_t *new_clauses = (kv_clause_t *)realloc(
        cnf->clauses,
        (size_t)(cnf->count + 1) * sizeof(kv_clause_t)
    );
    if (!new_clauses) return false;
    cnf->clauses = new_clauses;

    /* Allocate and copy literals */
    cnf->clauses[cnf->count].literals = (int *)malloc((size_t)count * sizeof(int));
    if (!cnf->clauses[cnf->count].literals) return false;

    memcpy(cnf->clauses[cnf->count].literals, lits, (size_t)count * sizeof(int));
    cnf->clauses[cnf->count].count = count;

    /* Update max_var */
    for (int i = 0; i < count; i++) {
        int var = lits[i] < 0 ? -lits[i] : lits[i];
        if (var > cnf->max_var) cnf->max_var = var;
    }

    cnf->count++;
    return true;
}

bool kv_latin_cnf(int n, kv_cnf_t *cnf) {
    if (n <= 0) return false;

    cnf->clauses = NULL;
    cnf->count = 0;
    cnf->max_var = 0;

    /* Pre-allocate clause buffer */
    int *clause = (int *)malloc((size_t)n * sizeof(int));
    int *pair = (int *)malloc(2 * sizeof(int));
    if (!clause || !pair) {
        free(clause);
        free(pair);
        return false;
    }

    /* For each cell (r, c) */
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < n; c++) {
            /* At least one digit: OR(v(r,c,0), v(r,c,1), ..., v(r,c,n-1)) */
            for (int d = 0; d < n; d++) {
                clause[d] = kv_var_cell_digit(n, r, c, d);
            }
            if (!cnf_add_clause(cnf, clause, n)) goto fail;

            /* At most one digit: for all pairs, NOT(both) */
            for (int d1 = 0; d1 < n; d1++) {
                for (int d2 = d1 + 1; d2 < n; d2++) {
                    pair[0] = -kv_var_cell_digit(n, r, c, d1);
                    pair[1] = -kv_var_cell_digit(n, r, c, d2);
                    if (!cnf_add_clause(cnf, pair, 2)) goto fail;
                }
            }
        }
    }

    /* Row uniqueness: each digit at most once per row */
    for (int r = 0; r < n; r++) {
        for (int d = 0; d < n; d++) {
            for (int c1 = 0; c1 < n; c1++) {
                for (int c2 = c1 + 1; c2 < n; c2++) {
                    pair[0] = -kv_var_cell_digit(n, r, c1, d);
                    pair[1] = -kv_var_cell_digit(n, r, c2, d);
                    if (!cnf_add_clause(cnf, pair, 2)) goto fail;
                }
            }
        }
    }

    /* Column uniqueness: each digit at most once per column */
    for (int c = 0; c < n; c++) {
        for (int d = 0; d < n; d++) {
            for (int r1 = 0; r1 < n; r1++) {
                for (int r2 = r1 + 1; r2 < n; r2++) {
                    pair[0] = -kv_var_cell_digit(n, r1, c, d);
                    pair[1] = -kv_var_cell_digit(n, r2, c, d);
                    if (!cnf_add_clause(cnf, pair, 2)) goto fail;
                }
            }
        }
    }

    free(clause);
    free(pair);
    return true;

fail:
    free(clause);
    free(pair);
    kv_free_cnf(cnf);
    return false;
}

bool kv_add_cage_cnf(int n,
                     const int *cells,
                     int num_cells,
                     int op,
                     int target,
                     bool killer,
                     kv_cnf_t *cnf) {
    /* For killer mode, add no-repeat constraints */
    if (killer) {
        int pair[2];
        for (int d = 0; d < n; d++) {
            for (int i = 0; i < num_cells; i++) {
                for (int j = i + 1; j < num_cells; j++) {
                    int r1 = cells[i] / n;
                    int c1 = cells[i] % n;
                    int r2 = cells[j] / n;
                    int c2 = cells[j] % n;

                    pair[0] = -kv_var_cell_digit(n, r1, c1, d);
                    pair[1] = -kv_var_cell_digit(n, r2, c2, d);
                    if (!cnf_add_clause(cnf, pair, 2)) return false;
                }
            }
        }
    }

    /* Cage arithmetic constraints would be encoded via Tseitin transformation
     * This is a simplified placeholder - full implementation would enumerate
     * valid tuples and create OR of AND clauses with auxiliary variables */

    (void)op;
    (void)target;

    return true;
}

void kv_free_cnf(kv_cnf_t *cnf) {
    if (!cnf) return;

    if (cnf->clauses) {
        for (int i = 0; i < cnf->count; i++) {
            free(cnf->clauses[i].literals);
        }
        free(cnf->clauses);
    }

    cnf->clauses = NULL;
    cnf->count = 0;
    cnf->max_var = 0;
}

int kv_write_dimacs(const kv_cnf_t *cnf, void *out) {
    FILE *f = (FILE *)out;
    if (!f || !cnf) return -1;

    /* DIMACS header */
    fprintf(f, "p cnf %d %d\n", cnf->max_var, cnf->count);

    /* Write clauses */
    for (int i = 0; i < cnf->count; i++) {
        for (int j = 0; j < cnf->clauses[i].count; j++) {
            fprintf(f, "%d ", cnf->clauses[i].literals[j]);
        }
        fprintf(f, "0\n");
    }

    return cnf->count;
}

/* ============================================================================
 * Integration Functions
 * ============================================================================ */

bool kv_validate_latin(int n, const int *grid) {
    if (n <= 0 || !grid) return false;

    /* Check value range */
    for (int i = 0; i < n * n; i++) {
        if (grid[i] < 1 || grid[i] > n) return false;
    }

    /* Check row uniqueness */
    for (int r = 0; r < n; r++) {
        for (int c1 = 0; c1 < n; c1++) {
            for (int c2 = c1 + 1; c2 < n; c2++) {
                if (grid[r * n + c1] == grid[r * n + c2]) return false;
            }
        }
    }

    /* Check column uniqueness */
    for (int c = 0; c < n; c++) {
        for (int r1 = 0; r1 < n; r1++) {
            for (int r2 = r1 + 1; r2 < n; r2++) {
                if (grid[r1 * n + c] == grid[r2 * n + c]) return false;
            }
        }
    }

    return true;
}

/* Note: kv_solve_latin_dlx would integrate with dlx.c
 * This requires linking with the existing DLX implementation */
