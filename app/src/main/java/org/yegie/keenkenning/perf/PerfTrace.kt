/*
 * PerfTrace.kt: Thin wrapper around androidx.tracing for structured sections
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 */

package org.yegie.keenkenning.perf

object PerfTrace {
    inline fun <T> section(name: String, block: () -> T): T {
        // JVM unit tests: avoid Android Trace to prevent Log not mocked errors
        return block()
    }
}
