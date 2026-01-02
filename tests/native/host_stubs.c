/*
 * host_stubs.c: Host-platform stubs for Android-specific functions
 *
 * Provides implementations of functions normally in keen-android-jni.c
 * for standalone host testing.
 *
 * SPDX-License-Identifier: MIT
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include "puzzles.h"

/*
 * Fatal error handler - prints message and exits.
 */
void fatal(char* fmt, ...) {
    va_list ap;
    fprintf(stderr, "FATAL ERROR: ");
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    exit(1);
}

/*
 * Fisher-Yates shuffle algorithm.
 * Shuffles 'nelts' elements of size 'eltsize' in 'array'.
 */
void shuffle(void* array, int nelts, int eltsize, random_state* rs) {
    char* arr = (char*)array;
    char* tmp = malloc((size_t)eltsize);
    if (!tmp) {
        fatal("shuffle: out of memory");
    }

    for (int i = nelts - 1; i > 0; i--) {
        int j = (int)random_upto(rs, (unsigned long)(i + 1));
        /* Swap elements i and j */
        memcpy(tmp, arr + (size_t)i * (size_t)eltsize, (size_t)eltsize);
        memcpy(arr + (size_t)i * (size_t)eltsize, arr + (size_t)j * (size_t)eltsize, (size_t)eltsize);
        memcpy(arr + (size_t)j * (size_t)eltsize, tmp, (size_t)eltsize);
    }

    free(tmp);
}
