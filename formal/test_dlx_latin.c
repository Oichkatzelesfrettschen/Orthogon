/**
 * @file test_dlx_latin.c
 * @brief Integration test for verified DLX Latin square solver
 *
 * Tests the complete pipeline:
 *   Coq proof -> OCaml extraction -> C (kv_*) -> DLX -> verified solution
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#include "dlx_latin_bridge.h"
#include <stdio.h>
#include <string.h>
#include <time.h>

/* ============================================================================
 * Test Utilities
 * ============================================================================ */

static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name) \
    do { \
        printf("  [TEST] %s... ", name); \
        tests_run++; \
    } while (0)

#define PASS() \
    do { \
        printf("PASS\n"); \
        tests_passed++; \
    } while (0)

#define FAIL(msg) \
    do { \
        printf("FAIL: %s\n", msg); \
    } while (0)

/**
 * @brief Print a Latin square grid
 */
static void print_grid(int n, const int *grid) {
    for (int r = 0; r < n; r++) {
        printf("    ");
        for (int c = 0; c < n; c++) {
            printf("%2d ", grid[r * n + c]);
        }
        printf("\n");
    }
}

/* ============================================================================
 * Test Cases
 * ============================================================================ */

/**
 * @brief Test matrix construction
 */
static void test_matrix_construction(void) {
    TEST("kv_build_latin_matrix(3)");

    kv_matrix_t matrix;
    if (!kv_build_latin_matrix(3, &matrix)) {
        FAIL("Failed to build matrix");
        return;
    }

    /* For n=3: rows = 27, cols = 27 */
    if (matrix.num_rows != 27) {
        FAIL("Wrong row count");
        kv_free_matrix(&matrix);
        return;
    }
    if (matrix.num_cols != 27) {
        FAIL("Wrong col count");
        kv_free_matrix(&matrix);
        return;
    }

    /* Each row should have exactly 3 columns */
    for (int i = 0; i < matrix.num_rows; i++) {
        if (matrix.rows[i].count != 3) {
            FAIL("Row should have 3 columns");
            kv_free_matrix(&matrix);
            return;
        }
    }

    kv_free_matrix(&matrix);
    PASS();
}

/**
 * @brief Test validation function
 */
static void test_validation(void) {
    TEST("kv_validate_latin valid grid");

    /* Valid 3x3 Latin square */
    int valid_grid[9] = {
        1, 2, 3,
        2, 3, 1,
        3, 1, 2
    };

    if (!kv_validate_latin(3, valid_grid)) {
        FAIL("Should validate valid grid");
        return;
    }
    PASS();

    TEST("kv_validate_latin invalid grid (row duplicate)");

    /* Invalid: row 0 has duplicate */
    int invalid_row[9] = {
        1, 1, 3,
        2, 3, 1,
        3, 2, 2
    };

    if (kv_validate_latin(3, invalid_row)) {
        FAIL("Should reject row duplicate");
        return;
    }
    PASS();

    TEST("kv_validate_latin invalid grid (column duplicate)");

    /* Invalid: column 0 has duplicate */
    int invalid_col[9] = {
        1, 2, 3,
        1, 3, 2,
        3, 1, 1
    };

    if (kv_validate_latin(3, invalid_col)) {
        FAIL("Should reject column duplicate");
        return;
    }
    PASS();
}

/**
 * @brief Test DLX solving for small grids
 */
static void test_dlx_solve_small(void) {
    for (int n = 3; n <= 5; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "kv_solve_latin_dlx(%d)", n);
        TEST(test_name);

        int *grid = (int *)calloc((size_t)(n * n), sizeof(int));
        if (!grid) {
            FAIL("Allocation failed");
            continue;
        }

        if (!kv_solve_latin_dlx(n, grid)) {
            FAIL("Solver failed");
            free(grid);
            continue;
        }

        /* Verify the solution */
        if (!kv_validate_latin(n, grid)) {
            FAIL("Solution invalid");
            printf("    Generated grid:\n");
            print_grid(n, grid);
            free(grid);
            continue;
        }

        free(grid);
        PASS();
    }
}

/**
 * @brief Test DLX solving with statistics
 */
static void test_dlx_solve_with_stats(void) {
    TEST("kv_solve_latin_dlx_stats(4)");

    int grid[16];
    dlx_latin_stats_t stats = kv_solve_latin_dlx_stats(4, grid);

    if (!stats.success) {
        FAIL("Solver failed");
        return;
    }

    /* Check expected matrix dimensions for n=4 */
    /* rows = 4^3 = 64, cols = 3 * 4^2 = 48 */
    if (stats.matrix_rows != 64) {
        FAIL("Wrong matrix rows");
        return;
    }
    if (stats.matrix_cols != 48) {
        FAIL("Wrong matrix cols");
        return;
    }
    if (stats.solution_rows != 16) {
        FAIL("Wrong solution size");
        return;
    }
    if (!stats.verified) {
        FAIL("Solution not verified");
        return;
    }

    PASS();

    printf("\n    Statistics for n=4:\n");
    printf("      Matrix: %d x %d\n", stats.matrix_rows, stats.matrix_cols);
    printf("      Ones: %d (density: %.2f%%)\n", stats.matrix_ones,
           100.0 * (double)stats.matrix_ones /
           ((double)stats.matrix_rows * (double)stats.matrix_cols));
    printf("      DLX nodes: %d\n", stats.dlx_nodes);
    printf("      Solution rows: %d\n", stats.solution_rows);
    printf("    Generated grid:\n");
    print_grid(4, grid);
}

/**
 * @brief Benchmark DLX solver for various sizes
 */
static void test_dlx_benchmark(void) {
    printf("\n=== DLX Benchmark ===\n");
    printf("  Size | Matrix     | Time (ms) | Verified\n");
    printf("  -----|------------|-----------|----------\n");

    for (int n = 3; n <= 9; n++) {
        int *grid = (int *)calloc((size_t)(n * n), sizeof(int));
        if (!grid) continue;

        clock_t start = clock();
        dlx_latin_stats_t stats = kv_solve_latin_dlx_stats(n, grid);
        clock_t end = clock();

        double ms = 1000.0 * (double)(end - start) / CLOCKS_PER_SEC;

        printf("  %4d | %4d x %3d | %9.2f | %s\n",
               n, stats.matrix_rows, stats.matrix_cols, ms,
               stats.verified ? "YES" : "NO");

        free(grid);

        /* Stop if taking too long */
        if (ms > 5000) {
            printf("  (stopping benchmark - too slow)\n");
            break;
        }
    }
}

/**
 * @brief Test exact cover checking
 */
static void test_exact_cover(void) {
    TEST("kv_is_exact_cover");

    /* Build a small matrix for testing */
    kv_matrix_t matrix;
    if (!kv_build_latin_matrix(2, &matrix)) {
        FAIL("Failed to build matrix");
        return;
    }

    /* For n=2: valid solution has 4 rows covering all 12 columns */
    /* Row indices for solution: (0,0,0), (0,1,1), (1,0,1), (1,1,0) */
    /* = rows 0, 3, 5, 6 in encoding r*n*n + c*n + v */
    int sol_indices[] = {0, 3, 5, 6};
    kv_solution_t solution = {
        .indices = sol_indices,
        .count = 4
    };

    if (!kv_is_exact_cover(&matrix, &solution)) {
        FAIL("Should recognize exact cover");
        kv_free_matrix(&matrix);
        return;
    }

    /* Invalid solution (missing a row) */
    int bad_indices[] = {0, 3, 5};
    kv_solution_t bad_solution = {
        .indices = bad_indices,
        .count = 3
    };

    if (kv_is_exact_cover(&matrix, &bad_solution)) {
        FAIL("Should reject incomplete cover");
        kv_free_matrix(&matrix);
        return;
    }

    kv_free_matrix(&matrix);
    PASS();
}

/* ============================================================================
 * Main
 * ============================================================================ */

int main(void) {
    printf("=== DLX Latin Square Integration Test ===\n");
    printf("  Testing verified DLX solver pipeline\n\n");

    /* Run tests */
    test_matrix_construction();
    test_validation();
    test_exact_cover();
    test_dlx_solve_small();
    test_dlx_solve_with_stats();
    test_dlx_benchmark();

    /* Summary */
    printf("\n=== Summary ===\n");
    printf("  Tests run: %d\n", tests_run);
    printf("  Tests passed: %d\n", tests_passed);
    printf("  Tests failed: %d\n", tests_run - tests_passed);

    return (tests_passed == tests_run) ? 0 : 1;
}
