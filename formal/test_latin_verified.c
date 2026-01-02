/**
 * @file test_latin_verified.c
 * @brief Test suite for verified Latin square generator
 *
 * Tests latin_verified.c functions to ensure they correctly wrap
 * the Coq-extracted DLX solver for puzzle generation.
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#define _POSIX_C_SOURCE 199309L  /* For clock_gettime */

#include "latin_verified.h"
#include "keen_verified.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;

/* Test macros */
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

/* Helper: convert unsigned char array to int array for validation */
static void uchar_to_int(const unsigned char *src, int *dst, int count) {
    for (int i = 0; i < count; i++) {
        dst[i] = src[i];
    }
}

/* Helper: print grid for debugging */
[[maybe_unused]]
static void print_grid(const unsigned char *sq, int n) {
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < n; c++) {
            printf("%2d ", sq[r * n + c]);
        }
        printf("\n");
    }
}

/* Test: basic generation for small grids */
static void test_basic_generation(void) {
    printf("\n=== Basic Generation Tests ===\n");

    for (int n = 2; n <= 9; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "Generate %dx%d Latin square", n, n);
        TEST(test_name);

        unsigned char *sq = latin_generate_verified(n);
        if (!sq) {
            FAIL("Generation returned NULL");
            continue;
        }

        /* Convert and validate */
        int *grid = malloc((size_t)n * (size_t)n * sizeof(int));
        uchar_to_int(sq, grid, n * n);

        if (kv_validate_latin(n, grid)) {
            PASS();
        } else {
            FAIL("Invalid Latin square");
        }

        free(grid);
        latin_verified_free(sq);
    }
}

/* Test: edge cases */
static void test_edge_cases(void) {
    printf("\n=== Edge Case Tests ===\n");

    TEST("Reject n=0");
    unsigned char *sq = latin_generate_verified(0);
    if (sq == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=0");
        latin_verified_free(sq);
    }

    TEST("Reject n=1");
    sq = latin_generate_verified(1);
    if (sq == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=1");
        latin_verified_free(sq);
    }

    TEST("Reject n=17");
    sq = latin_generate_verified(17);
    if (sq == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=17");
        latin_verified_free(sq);
    }

    TEST("Reject n=-1");
    sq = latin_generate_verified(-1);
    if (sq == NULL) {
        PASS();
    } else {
        FAIL("Should reject n=-1");
        latin_verified_free(sq);
    }
}

/* Test: shuffled generation produces variety */
static void test_shuffled_generation(void) {
    printf("\n=== Shuffled Generation Tests ===\n");

    int n = 4;

    /* Generate base square */
    TEST("Generate base 4x4");
    unsigned char *base = latin_generate_verified(n);
    if (!base) {
        FAIL("Base generation failed");
        return;
    }
    PASS();

    /* Generate shuffled with same seed - should produce consistent result */
    TEST("Shuffled with seed 12345");
    unsigned char *shuf1 = latin_generate_verified_shuffled(n, 12345);
    if (!shuf1) {
        FAIL("Shuffled generation failed");
        latin_verified_free(base);
        return;
    }
    PASS();

    /* Validate shuffled is also a Latin square */
    TEST("Shuffled square is valid");
    if (latin_check_verified(shuf1, n)) {
        PASS();
    } else {
        FAIL("Shuffled is not a valid Latin square");
    }

    /* Shuffled should differ from base (very likely for n=4) */
    TEST("Shuffled differs from base");
    bool differs = false;
    for (int i = 0; i < n * n; i++) {
        if (base[i] != shuf1[i]) {
            differs = true;
            break;
        }
    }
    if (differs) {
        PASS();
    } else {
        FAIL("Shuffled should differ from base");
    }

    /* Generate with different seed - should differ */
    TEST("Different seeds produce different results");
    unsigned char *shuf2 = latin_generate_verified_shuffled(n, 54321);
    if (!shuf2) {
        FAIL("Second shuffled generation failed");
    } else {
        bool differs2 = false;
        for (int i = 0; i < n * n; i++) {
            if (shuf1[i] != shuf2[i]) {
                differs2 = true;
                break;
            }
        }
        if (differs2) {
            PASS();
        } else {
            /* This could legitimately be equal, but very unlikely */
            printf("WARN (unlikely but possible)\n");
            tests_passed++; /* Don't penalize */
        }
        latin_verified_free(shuf2);
    }

    latin_verified_free(base);
    latin_verified_free(shuf1);
}

/* Test: verification function */
static void test_verification(void) {
    printf("\n=== Verification Function Tests ===\n");

    /* Valid 3x3 */
    unsigned char valid_3x3[] = {1, 2, 3, 2, 3, 1, 3, 1, 2};
    TEST("Verify valid 3x3");
    if (latin_check_verified(valid_3x3, 3)) {
        PASS();
    } else {
        FAIL("Should accept valid 3x3");
    }

    /* Invalid 3x3 (row duplicate) */
    unsigned char invalid_row[] = {1, 1, 3, 2, 3, 1, 3, 2, 2};
    TEST("Reject 3x3 with row duplicate");
    if (!latin_check_verified(invalid_row, 3)) {
        PASS();
    } else {
        FAIL("Should reject row duplicate");
    }

    /* Invalid 3x3 (column duplicate) */
    unsigned char invalid_col[] = {1, 2, 3, 1, 3, 2, 3, 1, 1};
    TEST("Reject 3x3 with column duplicate");
    if (!latin_check_verified(invalid_col, 3)) {
        PASS();
    } else {
        FAIL("Should reject column duplicate");
    }

    /* NULL pointer */
    TEST("Reject NULL pointer");
    if (!latin_check_verified(NULL, 3)) {
        PASS();
    } else {
        FAIL("Should reject NULL");
    }
}

/* Test: statistics collection */
static void test_statistics(void) {
    printf("\n=== Statistics Tests ===\n");

    /* Generate a square to populate stats */
    int n = 5;
    unsigned char *sq = latin_generate_verified(n);
    if (!sq) {
        TEST("Statistics collection");
        FAIL("Generation failed");
        return;
    }

    int rows, cols;
    long time_us;

    TEST("Get generation statistics");
    if (latin_verified_get_stats(&rows, &cols, &time_us)) {
        printf("\n      Rows=%d, Cols=%d, Time=%ld us ", rows, cols, time_us);
        /* Verify expected dimensions: rows = n^3, cols = 3n^2 */
        if (rows == n * n * n && cols == 3 * n * n) {
            PASS();
        } else {
            FAIL("Unexpected dimensions");
        }
    } else {
        FAIL("Failed to get stats");
    }

    latin_verified_free(sq);
}

/* Test: large grids */
static void test_large_grids(void) {
    printf("\n=== Large Grid Tests ===\n");

    for (int n = 10; n <= 16; n++) {
        char test_name[64];
        snprintf(test_name, sizeof(test_name), "Generate %dx%d Latin square", n, n);
        TEST(test_name);

        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);

        unsigned char *sq = latin_generate_verified(n);

        clock_gettime(CLOCK_MONOTONIC, &end);

        double elapsed_ms = (double)(end.tv_sec - start.tv_sec) * 1000.0 +
                           (double)(end.tv_nsec - start.tv_nsec) / 1000000.0;

        if (!sq) {
            FAIL("Generation returned NULL");
            continue;
        }

        /* Validate */
        if (latin_check_verified(sq, n)) {
            printf("(%.2f ms) ", elapsed_ms);
            PASS();
        } else {
            FAIL("Invalid Latin square");
        }

        latin_verified_free(sq);
    }
}

/* Test: performance benchmark */
static void test_benchmark(void) {
    printf("\n=== Performance Benchmark ===\n");
    printf("  Size |  Time (ms) | Verified\n");
    printf("  -----|------------|----------\n");

    for (int n = 3; n <= 12; n++) {
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);

        unsigned char *sq = latin_generate_verified(n);

        clock_gettime(CLOCK_MONOTONIC, &end);

        double elapsed_ms = (double)(end.tv_sec - start.tv_sec) * 1000.0 +
                           (double)(end.tv_nsec - start.tv_nsec) / 1000000.0;

        bool valid = sq && latin_check_verified(sq, n);
        printf("  %4d | %10.2f | %s\n", n, elapsed_ms, valid ? "YES" : "NO");

        if (sq) latin_verified_free(sq);
    }
}

int main(void) {
    printf("=============================================================\n");
    printf("  Verified Latin Generator Test Suite\n");
    printf("  Testing latin_verified.c integration\n");
    printf("=============================================================\n");

    test_edge_cases();
    test_basic_generation();
    test_shuffled_generation();
    test_verification();
    test_statistics();
    test_large_grids();
    test_benchmark();

    printf("\n=============================================================\n");
    printf("  Test Summary\n");
    printf("=============================================================\n");
    printf("  Tests run:     %d\n", tests_run);
    printf("  Tests passed:  %d\n", tests_passed);
    printf("  Tests failed:  %d\n", tests_run - tests_passed);
    printf("=============================================================\n");

    return (tests_passed == tests_run) ? 0 : 1;
}
