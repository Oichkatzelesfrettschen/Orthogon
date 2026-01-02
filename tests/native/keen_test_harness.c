/*
 * keen_test_harness.c: Exhaustive test harness for Keen puzzle generation
 *
 * Tests all combinations of grid sizes (3-9) and difficulty levels (0-6).
 * Reports success/failure statistics and timing data.
 *
 * Build with coverage instrumentation via CMakeLists.txt.
 *
 * SPDX-License-Identifier: MIT
 */

#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdbool.h>

#include "keen.h"
#include "keen_internal.h"
#include "puzzles.h"

/* Test configuration */
#define MIN_GRID_SIZE 3
#define MAX_GRID_SIZE 9      /* Full grid range for exhaustive testing */
#define NUM_DIFFICULTIES 7   /* All difficulties: EASY through INCOMPREHENSIBLE */
#define PUZZLES_PER_COMBO 5  /* Multiple samples per combination */
#define MAX_ATTEMPTS 25      /* Reasonable retry budget */

/* Difficulty names */
static const char* DIFF_NAMES[] = {
    "Easy", "Normal", "Hard", "Extreme",
    "Unreasonable", "Ludicrous", "Incomprehensible"
};

/* Test result tracking */
typedef struct {
    int size;
    int diff;
    int attempts;
    int successes;
    int failures;
    double avg_attempts;
    double total_time_ms;
} TestResult;

/* Statistics */
static int total_tests = 0;
static int total_successes = 0;
static int total_failures = 0;
static TestResult results[(MAX_GRID_SIZE - MIN_GRID_SIZE + 1) * NUM_DIFFICULTIES];

/* Timer helper */
static double get_time_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

/* Test a single grid size / difficulty combination */
static TestResult test_combination(int size, int diff, unsigned int base_seed) {
    TestResult result = {
        .size = size,
        .diff = diff,
        .attempts = 0,
        .successes = 0,
        .failures = 0,
        .avg_attempts = 0.0,
        .total_time_ms = 0.0
    };

    int total_attempts = 0;
    double start_time = get_time_ms();

    for (int puzzle = 0; puzzle < PUZZLES_PER_COMBO; puzzle++) {
        bool success = false;
        int attempts = 0;

        while (!success && attempts < MAX_ATTEMPTS) {
            attempts++;
            total_attempts++;

            /* Create seed string from base_seed + puzzle + attempt */
            char seed_str[64];
            snprintf(seed_str, sizeof(seed_str), "test_%u_%d_%d",
                     base_seed + (unsigned int)puzzle, puzzle, attempts);

            /* Create random state */
            random_state* rs = random_new(seed_str, (int)strlen(seed_str));
            if (!rs) {
                fprintf(stderr, "ERROR: Failed to create random state\n");
                continue;
            }

            /* Set up parameters */
            game_params params = {
                .w = size,
                .diff = diff,
                .multiplication_only = 0,
                .mode_flags = 0
            };

            /* Generate puzzle */
            char* aux = NULL;
            char* desc = new_game_desc(&params, rs, &aux, 0);

            if (desc != NULL) {
                success = true;
                result.successes++;
                /* Free resources */
                sfree(desc);
                if (aux) sfree(aux);
            }

            random_free(rs);
        }

        if (!success) {
            result.failures++;
        }
        result.attempts += attempts;
    }

    result.total_time_ms = get_time_ms() - start_time;
    result.avg_attempts = (double)total_attempts / PUZZLES_PER_COMBO;

    return result;
}

/* Print a progress bar */
static void print_progress(int current, int total) {
    int width = 50;
    int pos = (current * width) / total;
    printf("\r[");
    for (int i = 0; i < width; i++) {
        if (i < pos) printf("=");
        else if (i == pos) printf(">");
        else printf(" ");
    }
    printf("] %d/%d", current, total);
    fflush(stdout);
}

/* Run all tests */
static void run_all_tests(void) {
    int num_combos = (MAX_GRID_SIZE - MIN_GRID_SIZE + 1) * NUM_DIFFICULTIES;
    int result_idx = 0;

    printf("Keen Puzzle Generation Test Harness\n");
    printf("====================================\n");
    printf("Grid sizes: %d to %d\n", MIN_GRID_SIZE, MAX_GRID_SIZE);
    printf("Difficulties: %d levels\n", NUM_DIFFICULTIES);
    printf("Puzzles per combo: %d\n", PUZZLES_PER_COMBO);
    printf("Max attempts per puzzle: %d\n", MAX_ATTEMPTS);
    printf("Total test combinations: %d\n\n", num_combos);

    unsigned int base_seed = (unsigned int)time(NULL);
    printf("Base seed: %u\n\n", base_seed);

    double overall_start = get_time_ms();

    for (int size = MIN_GRID_SIZE; size <= MAX_GRID_SIZE; size++) {
        for (int diff = 0; diff < NUM_DIFFICULTIES; diff++) {
            int current = (size - MIN_GRID_SIZE) * NUM_DIFFICULTIES + diff;
            print_progress(current, num_combos);

            results[result_idx] = test_combination(size, diff,
                base_seed + (unsigned int)(current * 1000));

            total_tests += PUZZLES_PER_COMBO;
            total_successes += results[result_idx].successes;
            total_failures += results[result_idx].failures;

            result_idx++;
        }
    }

    double overall_time = get_time_ms() - overall_start;
    print_progress(num_combos, num_combos);
    printf("\n\n");

    /* Print results table */
    printf("Results Matrix (successes / %d puzzles per cell):\n", PUZZLES_PER_COMBO);
    printf("%-8s", "Size");
    for (int d = 0; d < NUM_DIFFICULTIES; d++) {
        printf(" %6.6s", DIFF_NAMES[d]);
    }
    printf("\n");
    printf("--------");
    for (int d = 0; d < NUM_DIFFICULTIES; d++) {
        printf(" ------");
    }
    printf("\n");

    result_idx = 0;
    for (int size = MIN_GRID_SIZE; size <= MAX_GRID_SIZE; size++) {
        printf("%dx%-5d", size, size);
        for (int d = 0; d < NUM_DIFFICULTIES; d++) {
            TestResult* r = &results[result_idx++];
            if (r->successes == PUZZLES_PER_COMBO) {
                printf("  %d/%d ", r->successes, PUZZLES_PER_COMBO);
            } else if (r->successes > 0) {
                printf("  %d/%d*", r->successes, PUZZLES_PER_COMBO);
            } else {
                printf("  FAIL ");
            }
        }
        printf("\n");
    }

    /* Print detailed failures */
    printf("\n");
    printf("Detailed Results (showing avg attempts and time):\n");
    printf("%-8s %-15s %8s %8s %10s\n",
           "Size", "Difficulty", "Success", "AvgAttempts", "Time(ms)");
    printf("-------- --------------- -------- ------------ ----------\n");

    result_idx = 0;
    for (int size = MIN_GRID_SIZE; size <= MAX_GRID_SIZE; size++) {
        for (int d = 0; d < NUM_DIFFICULTIES; d++) {
            TestResult* r = &results[result_idx++];
            const char* status = (r->successes == PUZZLES_PER_COMBO) ? "PASS" :
                                 (r->successes > 0) ? "PARTIAL" : "FAIL";
            printf("%dx%-5d %-15s %8s %12.1f %10.1f\n",
                   size, size, DIFF_NAMES[d], status,
                   r->avg_attempts, r->total_time_ms);
        }
    }

    /* Summary */
    printf("\n");
    printf("Summary\n");
    printf("=======\n");
    printf("Total puzzles attempted: %d\n", total_tests);
    printf("Successful generations:  %d (%.1f%%)\n",
           total_successes, 100.0 * total_successes / total_tests);
    printf("Failed generations:      %d (%.1f%%)\n",
           total_failures, 100.0 * total_failures / total_tests);
    printf("Total time:              %.1f ms\n", overall_time);
    printf("Avg time per puzzle:     %.1f ms\n", overall_time / total_tests);

    /* Exit code based on success rate */
    if (total_failures > 0) {
        printf("\nWARNING: Some puzzle generations failed!\n");
    } else {
        printf("\nAll tests passed!\n");
    }
}

int main(int argc, char* argv[]) {
    (void)argc;
    (void)argv;

    run_all_tests();

    return (total_failures > 0) ? 1 : 0;
}
