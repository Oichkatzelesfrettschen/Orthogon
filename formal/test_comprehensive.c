/**
 * @file test_comprehensive.c
 * @brief Comprehensive grid size and difficulty tests for verified DLX solver
 *
 * Tests all grid sizes from 2x2 through 16x16 with performance benchmarks
 * and validates the mathematical properties of Latin square generation.
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#include "dlx_latin_bridge.h"
#include "keen_verified.h"
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>

/* ============================================================================
 * Test Framework
 * ============================================================================ */

static int tests_run = 0;
static int tests_passed = 0;
static int tests_skipped = 0;

#define TEST(name) \
    do { \
        printf("  [TEST] %-50s ", name); \
        fflush(stdout); \
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

#define SKIP(msg) \
    do { \
        printf("SKIP: %s\n", msg); \
        tests_skipped++; \
        tests_passed++; /* Count skips as non-failures */ \
    } while (0)

/* ============================================================================
 * Utility Functions
 * ============================================================================ */

/**
 * @brief Print a Latin square grid
 */
static void print_grid(int n, const int *grid) {
    printf("\n");
    for (int r = 0; r < n; r++) {
        printf("      ");
        for (int c = 0; c < n; c++) {
            if (n <= 9) {
                printf("%d ", grid[r * n + c]);
            } else {
                /* Hex for larger grids */
                int v = grid[r * n + c];
                if (v <= 9) {
                    printf("%d ", v);
                } else {
                    printf("%c ", 'A' + (v - 10));
                }
            }
        }
        printf("\n");
    }
}

/**
 * @brief Count distinct Latin squares for small n (reference)
 * Used for future diversity testing
 */
[[maybe_unused]]
static long long known_latin_count(int n) {
    /* Known values from combinatorics literature */
    switch (n) {
        case 1: return 1;
        case 2: return 2;
        case 3: return 12;
        case 4: return 576;
        case 5: return 161280;
        case 6: return 812851200LL;
        default: return -1; /* Unknown/too large */
    }
}

/**
 * @brief Check if grid values are in valid range
 */
static bool check_value_range(int n, const int *grid, int min_val) {
    for (int i = 0; i < n * n; i++) {
        if (grid[i] < min_val || grid[i] >= min_val + n) {
            return false;
        }
    }
    return true;
}

/**
 * @brief Count row/column violations
 */
static int count_violations(int n, const int *grid) {
    int violations = 0;

    /* Row violations */
    for (int r = 0; r < n; r++) {
        for (int c1 = 0; c1 < n; c1++) {
            for (int c2 = c1 + 1; c2 < n; c2++) {
                if (grid[r * n + c1] == grid[r * n + c2]) {
                    violations++;
                }
            }
        }
    }

    /* Column violations */
    for (int c = 0; c < n; c++) {
        for (int r1 = 0; r1 < n; r1++) {
            for (int r2 = r1 + 1; r2 < n; r2++) {
                if (grid[r1 * n + c] == grid[r2 * n + c]) {
                    violations++;
                }
            }
        }
    }

    return violations;
}

/* ============================================================================
 * Grid Size Tests (2x2 through 16x16)
 * ============================================================================ */

/**
 * @brief Test 2x2 Latin square (edge case - trivial)
 */
static void test_2x2_latin(void) {
    TEST("2x2 Latin square generation");

    /* 2x2 is mathematically trivial but we test it anyway */
    int grid[4];

    if (!kv_solve_latin_dlx(2, grid)) {
        FAIL("Solver failed for n=2");
        return;
    }

    /* Validate */
    if (!kv_validate_latin(2, grid)) {
        FAIL("Invalid Latin square generated");
        print_grid(2, grid);
        return;
    }

    /* Check value range [1,2] */
    if (!check_value_range(2, grid, 1)) {
        FAIL("Values out of range");
        return;
    }

    PASS();
    printf("      Generated: ");
    for (int i = 0; i < 4; i++) printf("%d ", grid[i]);
    printf("\n");
}

/**
 * @brief Test all grid sizes from 3 to max_n
 */
static void test_grid_sizes(int max_n) {
    printf("\n=== Grid Size Tests (3 to %d) ===\n", max_n);

    for (int n = 3; n <= max_n; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "%dx%d Latin square generation", n, n);
        TEST(test_name);

        int *grid = (int *)calloc((size_t)(n * n), sizeof(int));
        if (!grid) {
            FAIL("Memory allocation failed");
            continue;
        }

        clock_t start = clock();
        bool success = kv_solve_latin_dlx(n, grid);
        clock_t end = clock();
        double ms = 1000.0 * (double)(end - start) / CLOCKS_PER_SEC;

        if (!success) {
            FAIL("Solver failed");
            free(grid);
            continue;
        }

        /* Validate */
        if (!kv_validate_latin(n, grid)) {
            FAIL("Invalid Latin square");
            print_grid(n, grid);
            free(grid);
            continue;
        }

        /* Count violations (should be 0) */
        int violations = count_violations(n, grid);
        if (violations > 0) {
            char msg[64];
            snprintf(msg, sizeof(msg), "%d violations found", violations);
            FAIL(msg);
            free(grid);
            continue;
        }

        free(grid);
        PASS();
        printf("      Time: %.2f ms\n", ms);

        /* Stop if taking too long */
        if (ms > 10000) {
            printf("      (stopping - exceeded 10s threshold)\n");
            break;
        }
    }
}

/* ============================================================================
 * Matrix Construction Tests
 * ============================================================================ */

/**
 * @brief Verify matrix dimensions for all sizes
 */
static void test_matrix_dimensions(void) {
    printf("\n=== Matrix Dimension Tests ===\n");

    for (int n = 2; n <= 9; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "Matrix dimensions for n=%d", n);
        TEST(test_name);

        kv_matrix_t matrix;
        if (!kv_build_latin_matrix(n, &matrix)) {
            FAIL("Failed to build matrix");
            continue;
        }

        /* Expected dimensions */
        int expected_rows = n * n * n;
        int expected_cols = 3 * n * n;

        if (matrix.num_rows != expected_rows) {
            char msg[64];
            snprintf(msg, sizeof(msg), "Expected %d rows, got %d",
                     expected_rows, matrix.num_rows);
            FAIL(msg);
            kv_free_matrix(&matrix);
            continue;
        }

        if (matrix.num_cols != expected_cols) {
            char msg[64];
            snprintf(msg, sizeof(msg), "Expected %d cols, got %d",
                     expected_cols, matrix.num_cols);
            FAIL(msg);
            kv_free_matrix(&matrix);
            continue;
        }

        /* Count total ones */
        int total_ones = 0;
        for (int r = 0; r < matrix.num_rows; r++) {
            total_ones += matrix.rows[r].count;
        }

        /* Each row should have exactly 3 ones */
        int expected_ones = 3 * expected_rows;
        if (total_ones != expected_ones) {
            char msg[64];
            snprintf(msg, sizeof(msg), "Expected %d ones, got %d",
                     expected_ones, total_ones);
            FAIL(msg);
            kv_free_matrix(&matrix);
            continue;
        }

        kv_free_matrix(&matrix);
        PASS();
    }
}

/* ============================================================================
 * CNF Encoding Tests
 * ============================================================================ */

/**
 * @brief Test CNF generation for various grid sizes
 */
static void test_cnf_generation(void) {
    printf("\n=== CNF Generation Tests ===\n");

    for (int n = 2; n <= 6; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "CNF encoding for n=%d", n);
        TEST(test_name);

        kv_cnf_t cnf;
        if (!kv_latin_cnf(n, &cnf)) {
            FAIL("Failed to generate CNF");
            continue;
        }

        /* Calculate expected clause counts */
        /* At-least-one: n^2 clauses (one per cell) */
        /* At-most-one per cell: n^2 * C(n,2) = n^2 * n*(n-1)/2 */
        /* Row uniqueness: n^2 * C(n,2) */
        /* Col uniqueness: n^2 * C(n,2) */
        int cells = n * n;
        int pairs = n * (n - 1) / 2;
        int expected_alo = cells;
        int expected_amo_cell = cells * pairs;
        int expected_row = n * n * pairs;
        int expected_col = n * n * pairs;
        int expected_total = expected_alo + expected_amo_cell + expected_row + expected_col;

        if (cnf.count != expected_total) {
            char msg[128];
            snprintf(msg, sizeof(msg), "Expected %d clauses, got %d",
                     expected_total, cnf.count);
            FAIL(msg);
            kv_free_cnf(&cnf);
            continue;
        }

        /* Verify max variable number */
        int expected_max_var = n * n * n; /* n^3 variables */
        if (cnf.max_var != expected_max_var) {
            char msg[64];
            snprintf(msg, sizeof(msg), "Expected max_var=%d, got %d",
                     expected_max_var, cnf.max_var);
            FAIL(msg);
            kv_free_cnf(&cnf);
            continue;
        }

        kv_free_cnf(&cnf);
        PASS();
        printf("      Clauses: %d, Variables: %d\n", expected_total, expected_max_var);
    }
}

/* ============================================================================
 * Validation Tests
 * ============================================================================ */

/**
 * @brief Test validation with known valid/invalid grids
 */
static void test_validation_comprehensive(void) {
    printf("\n=== Comprehensive Validation Tests ===\n");

    /* Valid 2x2 */
    TEST("Validate valid 2x2");
    {
        int grid[] = {1, 2, 2, 1};
        if (kv_validate_latin(2, grid)) {
            PASS();
        } else {
            FAIL("Should accept valid grid");
        }
    }

    /* Invalid 2x2 - same row */
    TEST("Reject 2x2 with row duplicate");
    {
        int grid[] = {1, 1, 2, 2};
        if (!kv_validate_latin(2, grid)) {
            PASS();
        } else {
            FAIL("Should reject row duplicate");
        }
    }

    /* Valid 3x3 */
    TEST("Validate valid 3x3");
    {
        int grid[] = {1, 2, 3, 2, 3, 1, 3, 1, 2};
        if (kv_validate_latin(3, grid)) {
            PASS();
        } else {
            FAIL("Should accept valid grid");
        }
    }

    /* Invalid 3x3 - column duplicate */
    TEST("Reject 3x3 with column duplicate");
    {
        int grid[] = {1, 2, 3, 1, 3, 2, 2, 1, 1};
        if (!kv_validate_latin(3, grid)) {
            PASS();
        } else {
            FAIL("Should reject column duplicate");
        }
    }

    /* Valid 4x4 */
    TEST("Validate valid 4x4");
    {
        int grid[] = {
            1, 2, 3, 4,
            2, 1, 4, 3,
            3, 4, 1, 2,
            4, 3, 2, 1
        };
        if (kv_validate_latin(4, grid)) {
            PASS();
        } else {
            FAIL("Should accept valid grid");
        }
    }

    /* Out of range value */
    TEST("Reject grid with out-of-range value");
    {
        int grid[] = {1, 2, 3, 5, 2, 3, 4, 1, 3, 4, 1, 2, 4, 1, 2, 3};
        if (!kv_validate_latin(4, grid)) {
            PASS();
        } else {
            FAIL("Should reject out-of-range value");
        }
    }

    /* Zero value */
    TEST("Reject grid with zero value");
    {
        int grid[] = {0, 2, 3, 4, 2, 3, 4, 1, 3, 4, 1, 2, 4, 1, 2, 3};
        if (!kv_validate_latin(4, grid)) {
            PASS();
        } else {
            FAIL("Should reject zero value");
        }
    }
}

/* ============================================================================
 * Exact Cover Tests
 * ============================================================================ */

/**
 * @brief Test exact cover property for various sizes
 */
static void test_exact_cover(void) {
    printf("\n=== Exact Cover Tests ===\n");

    for (int n = 2; n <= 5; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "Exact cover verification for n=%d", n);
        TEST(test_name);

        kv_matrix_t matrix;
        if (!kv_build_latin_matrix(n, &matrix)) {
            FAIL("Failed to build matrix");
            continue;
        }

        /* Solve and get solution rows */
        int *grid = (int *)calloc((size_t)(n * n), sizeof(int));
        if (!grid) {
            FAIL("Memory allocation failed");
            kv_free_matrix(&matrix);
            continue;
        }

        dlx_latin_stats_t stats = kv_solve_latin_dlx_stats(n, grid);

        if (!stats.success) {
            FAIL("Solver failed");
            free(grid);
            kv_free_matrix(&matrix);
            continue;
        }

        /* Verify solution size */
        if (stats.solution_rows != n * n) {
            char msg[64];
            snprintf(msg, sizeof(msg), "Expected %d solution rows, got %d",
                     n * n, stats.solution_rows);
            FAIL(msg);
            free(grid);
            kv_free_matrix(&matrix);
            continue;
        }

        free(grid);
        kv_free_matrix(&matrix);
        PASS();
    }
}

/* ============================================================================
 * Performance Benchmark
 * ============================================================================ */

/**
 * @brief Benchmark DLX solver across all sizes
 */
static void benchmark_all_sizes(void) {
    printf("\n=== Performance Benchmark ===\n");
    printf("  Size | Rows    | Cols | Nodes  | Time (ms) | Valid\n");
    printf("  -----|---------|------|--------|-----------|------\n");

    for (int n = 2; n <= 12; n++) {
        int *grid = (int *)calloc((size_t)(n * n), sizeof(int));
        if (!grid) continue;

        clock_t start = clock();
        dlx_latin_stats_t stats = kv_solve_latin_dlx_stats(n, grid);
        clock_t end = clock();
        double ms = 1000.0 * (double)(end - start) / CLOCKS_PER_SEC;

        printf("  %4d | %7d | %4d | %6d | %9.2f | %s\n",
               n, stats.matrix_rows, stats.matrix_cols,
               stats.dlx_nodes, ms,
               stats.verified ? "YES" : "NO");

        free(grid);

        /* Stop if too slow */
        if (ms > 30000) {
            printf("  (stopping benchmark - exceeded 30s)\n");
            break;
        }
    }
}

/* ============================================================================
 * Edge Cases and Stress Tests
 * ============================================================================ */

/**
 * @brief Test edge cases
 */
static void test_edge_cases(void) {
    printf("\n=== Edge Case Tests ===\n");

    /* n=0 should fail */
    TEST("Reject n=0");
    {
        int grid[1];
        if (!kv_solve_latin_dlx(0, grid)) {
            PASS();
        } else {
            FAIL("Should reject n=0");
        }
    }

    /* n=1 is trivial but valid */
    TEST("Handle n=1 (trivial case)");
    {
        int grid[1] = {0};
        if (kv_solve_latin_dlx(1, grid)) {
            if (grid[0] == 1 && kv_validate_latin(1, grid)) {
                PASS();
            } else {
                FAIL("Invalid result for n=1");
            }
        } else {
            FAIL("Solver failed for n=1");
        }
    }

    /* NULL pointer handling */
    TEST("Handle NULL solution pointer");
    {
        if (!kv_solve_latin_dlx(3, NULL)) {
            PASS();
        } else {
            FAIL("Should reject NULL pointer");
        }
    }

    /* Negative n */
    TEST("Reject negative n");
    {
        int grid[1];
        if (!kv_solve_latin_dlx(-1, grid)) {
            PASS();
        } else {
            FAIL("Should reject negative n");
        }
    }

    /* Very large n (should fail gracefully) */
    TEST("Handle n=17 (exceeds limit)");
    {
        int grid[289];
        if (!kv_solve_latin_dlx(17, grid)) {
            PASS();
        } else {
            FAIL("Should reject n > 16");
        }
    }
}

/* ============================================================================
 * Main
 * ============================================================================ */

int main(int argc, char *argv[]) {
    int max_size = 9;

    /* Allow command-line override for max size */
    if (argc > 1) {
        max_size = atoi(argv[1]);
        if (max_size < 2) max_size = 2;
        if (max_size > 16) max_size = 16;
    }

    printf("=============================================================\n");
    printf("  Comprehensive DLX Latin Square Test Suite\n");
    printf("  Testing grid sizes 2x2 through %dx%d\n", max_size, max_size);
    printf("=============================================================\n");

    /* Run all test suites */
    test_edge_cases();
    test_2x2_latin();
    test_validation_comprehensive();
    test_matrix_dimensions();
    test_cnf_generation();
    test_exact_cover();
    test_grid_sizes(max_size);
    benchmark_all_sizes();

    /* Summary */
    printf("\n=============================================================\n");
    printf("  Test Summary\n");
    printf("=============================================================\n");
    printf("  Tests run:     %d\n", tests_run);
    printf("  Tests passed:  %d\n", tests_passed);
    printf("  Tests skipped: %d\n", tests_skipped);
    printf("  Tests failed:  %d\n", tests_run - tests_passed);
    printf("=============================================================\n");

    return (tests_passed == tests_run) ? 0 : 1;
}
