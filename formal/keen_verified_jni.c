/**
 * @file keen_verified_jni.c
 * @brief Implementation of JNI-compatible interface for verified solver
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#define _POSIX_C_SOURCE 199309L  /* For clock_gettime */

#include "keen_verified_jni.h"
#include "latin_verified.h"

#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Version string */
static const char *VERSION_STRING =
    "KeenKenning Verified Solver v1.0 (Coq-extracted, DLX backend)";

int8_t *kv_jni_generate_latin(int n, bool shuffle, uint32_t seed,
                               kv_jni_stats_t *out_stats) {
    /* Initialize stats */
    kv_jni_stats_t stats = {
        .success = false,
        .verified = false,
        .grid_size = n,
        .solve_time_ms = 0,
        .matrix_rows = 0,
        .matrix_cols = 0
    };

    /* Validate size */
    if (n < KV_JNI_MIN_SIZE || n > KV_JNI_MAX_SIZE) {
        if (out_stats) *out_stats = stats;
        return NULL;
    }

    /* Time the generation */
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);

    /* Generate Latin square */
    unsigned char *uchar_grid;
    if (shuffle) {
        uchar_grid = latin_generate_verified_shuffled(n, seed);
    } else {
        uchar_grid = latin_generate_verified(n);
    }

    clock_gettime(CLOCK_MONOTONIC, &end);

    /* Calculate elapsed time */
    long elapsed_us = (end.tv_sec - start.tv_sec) * 1000000L +
                      (end.tv_nsec - start.tv_nsec) / 1000L;
    stats.solve_time_ms = (int)(elapsed_us / 1000);

    if (!uchar_grid) {
        if (out_stats) *out_stats = stats;
        return NULL;
    }

    /* Get internal statistics */
    int rows, cols;
    long time_us;
    if (latin_verified_get_stats(&rows, &cols, &time_us)) {
        stats.matrix_rows = rows;
        stats.matrix_cols = cols;
    }

    /* Validate result */
    stats.verified = latin_check_verified(uchar_grid, n);
    stats.success = stats.verified;

    if (!stats.verified) {
        latin_verified_free(uchar_grid);
        if (out_stats) *out_stats = stats;
        return NULL;
    }

    /* Convert unsigned char to int8_t for JNI compatibility */
    int8_t *grid = malloc((size_t)n * (size_t)n * sizeof(int8_t));
    if (!grid) {
        latin_verified_free(uchar_grid);
        stats.success = false;
        if (out_stats) *out_stats = stats;
        return NULL;
    }

    for (int i = 0; i < n * n; i++) {
        grid[i] = (int8_t)uchar_grid[i];
    }

    latin_verified_free(uchar_grid);

    if (out_stats) *out_stats = stats;
    return grid;
}

void kv_jni_free_grid(int8_t *grid) {
    free(grid);
}

bool kv_jni_validate_latin(const int8_t *grid, int n) {
    if (!grid || n < 1 || n > KV_JNI_MAX_SIZE) {
        return false;
    }

    /* Convert to unsigned char for validation */
    unsigned char *uchar_grid = malloc((size_t)n * (size_t)n * sizeof(unsigned char));
    if (!uchar_grid) {
        return false;
    }

    for (int i = 0; i < n * n; i++) {
        uchar_grid[i] = (unsigned char)grid[i];
    }

    bool valid = latin_check_verified(uchar_grid, n);
    free(uchar_grid);
    return valid;
}

bool kv_jni_is_available(void) {
    /* Verify the solver works by generating a small test square */
    unsigned char *test = latin_generate_verified(3);
    if (!test) {
        return false;
    }

    bool valid = latin_check_verified(test, 3);
    latin_verified_free(test);
    return valid;
}

const char *kv_jni_version(void) {
    return VERSION_STRING;
}
