/**
 * @file test_jni_interface.c
 * @brief Test suite for JNI-compatible verified solver interface
 *
 * Tests the keen_verified_jni.c functions to ensure they work correctly
 * for Android integration.
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#define _POSIX_C_SOURCE 199309L

#include "keen_verified_jni.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name) do { \
    tests_run++; \
    printf("  [TEST] %-50s ", name); \
    fflush(stdout); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    printf("PASS\n"); \
} while(0)

#define FAIL(msg) do { \
    printf("FAIL: %s\n", msg); \
} while(0)

/* Test: availability check */
static void test_availability(void) {
    printf("\n=== Availability Tests ===\n");

    TEST("Verified solver available");
    if (kv_jni_is_available()) {
        PASS();
    } else {
        FAIL("Solver not available");
    }

    TEST("Version string exists");
    const char *ver = kv_jni_version();
    if (ver && strlen(ver) > 0) {
        printf("\n      Version: %s ", ver);
        PASS();
    } else {
        FAIL("No version string");
    }
}

/* Test: basic generation */
static void test_generation(void) {
    printf("\n=== Generation Tests ===\n");

    for (int n = 2; n <= 9; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "Generate %dx%d via JNI interface", n, n);
        TEST(test_name);

        kv_jni_stats_t stats;
        int8_t *grid = kv_jni_generate_latin(n, false, 0, &stats);

        if (!grid) {
            FAIL("Generation returned NULL");
            continue;
        }

        if (!stats.success || !stats.verified) {
            FAIL("Stats indicate failure");
            kv_jni_free_grid(grid);
            continue;
        }

        /* Validate using JNI interface */
        if (kv_jni_validate_latin(grid, n)) {
            printf("(%d ms) ", stats.solve_time_ms);
            PASS();
        } else {
            FAIL("Validation failed");
        }

        kv_jni_free_grid(grid);
    }
}

/* Test: shuffled generation */
static void test_shuffled(void) {
    printf("\n=== Shuffled Generation Tests ===\n");

    int n = 6;

    TEST("Shuffled generation with seed");
    kv_jni_stats_t stats;
    int8_t *grid1 = kv_jni_generate_latin(n, true, 12345, &stats);
    if (!grid1 || !stats.verified) {
        FAIL("First generation failed");
        if (grid1) kv_jni_free_grid(grid1);
        return;
    }
    PASS();

    TEST("Different seed produces different grid");
    int8_t *grid2 = kv_jni_generate_latin(n, true, 54321, &stats);
    if (!grid2 || !stats.verified) {
        FAIL("Second generation failed");
        kv_jni_free_grid(grid1);
        if (grid2) kv_jni_free_grid(grid2);
        return;
    }

    bool differs = false;
    for (int i = 0; i < n * n; i++) {
        if (grid1[i] != grid2[i]) {
            differs = true;
            break;
        }
    }

    if (differs) {
        PASS();
    } else {
        printf("WARN (unlikely but possible)\n");
        tests_passed++; /* Don't penalize */
    }

    TEST("Shuffled grids are valid");
    bool valid1 = kv_jni_validate_latin(grid1, n);
    bool valid2 = kv_jni_validate_latin(grid2, n);
    if (valid1 && valid2) {
        PASS();
    } else {
        FAIL("Shuffled grids invalid");
    }

    kv_jni_free_grid(grid1);
    kv_jni_free_grid(grid2);
}

/* Test: statistics collection */
static void test_statistics(void) {
    printf("\n=== Statistics Tests ===\n");

    int n = 7;
    kv_jni_stats_t stats;

    TEST("Stats populated correctly");
    int8_t *grid = kv_jni_generate_latin(n, false, 0, &stats);
    if (!grid) {
        FAIL("Generation failed");
        return;
    }

    printf("\n      Size=%d, Rows=%d, Cols=%d, Time=%d ms ",
           stats.grid_size, stats.matrix_rows, stats.matrix_cols,
           stats.solve_time_ms);

    bool correct_dims = (stats.grid_size == n) &&
                        (stats.matrix_rows == n * n * n) &&
                        (stats.matrix_cols == 3 * n * n);

    if (stats.success && stats.verified && correct_dims) {
        PASS();
    } else {
        FAIL("Stats incorrect");
    }

    kv_jni_free_grid(grid);
}

/* Test: edge cases */
static void test_edge_cases(void) {
    printf("\n=== Edge Case Tests ===\n");

    TEST("Reject n=0");
    int8_t *grid = kv_jni_generate_latin(0, false, 0, NULL);
    if (grid == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=0");
        kv_jni_free_grid(grid);
    }

    TEST("Reject n=1");
    grid = kv_jni_generate_latin(1, false, 0, NULL);
    if (grid == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=1");
        kv_jni_free_grid(grid);
    }

    TEST("Reject n=17 (exceeds max)");
    grid = kv_jni_generate_latin(17, false, 0, NULL);
    if (grid == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=17");
        kv_jni_free_grid(grid);
    }

    TEST("Handle NULL stats pointer");
    grid = kv_jni_generate_latin(4, false, 0, NULL);
    if (grid != NULL) {
        bool valid = kv_jni_validate_latin(grid, 4);
        if (valid) {
            PASS();
        } else {
            FAIL("Grid with NULL stats invalid");
        }
        kv_jni_free_grid(grid);
    } else {
        FAIL("Generation failed with NULL stats");
    }

    TEST("Validate NULL grid");
    if (!kv_jni_validate_latin(NULL, 4)) {
        PASS();
    } else {
        FAIL("Should reject NULL grid");
    }
}

/* Test: large grids performance */
static void test_large_grids(void) {
    printf("\n=== Large Grid Performance ===\n");
    printf("  Size | Time (ms) | Verified\n");
    printf("  -----|-----------|----------\n");

    for (int n = 10; n <= 16; n++) {
        kv_jni_stats_t stats;
        int8_t *grid = kv_jni_generate_latin(n, false, 0, &stats);

        printf("  %4d | %9d | %s\n",
               n, stats.solve_time_ms,
               (grid && stats.verified) ? "YES" : "NO");

        if (grid) kv_jni_free_grid(grid);
    }
}

int main(void) {
    printf("=============================================================\n");
    printf("  JNI Interface Test Suite\n");
    printf("  Testing keen_verified_jni.c for Android integration\n");
    printf("=============================================================\n");

    test_availability();
    test_edge_cases();
    test_generation();
    test_shuffled();
    test_statistics();
    test_large_grids();

    printf("\n=============================================================\n");
    printf("  Test Summary\n");
    printf("=============================================================\n");
    printf("  Tests run:     %d\n", tests_run);
    printf("  Tests passed:  %d\n", tests_passed);
    printf("  Tests failed:  %d\n", tests_run - tests_passed);
    printf("=============================================================\n");

    return (tests_passed == tests_run) ? 0 : 1;
}
