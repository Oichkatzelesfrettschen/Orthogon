/*
 * GameTheme.kt: Custom theme and color definitions
 *
 * SPDX-License-Identifier: MIT
 * SPDX-FileCopyrightText: Copyright (C) 2024-2025 KeenKenning Contributors
 */

package org.yegie.keenkenning.ui.theme

import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.staticCompositionLocalOf
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.TextUnit
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.sp

/**
 * Accessible Game Theme System
 *
 * Design principles:
 * - WCAG AA compliant (4.5:1 contrast minimum for text)
 * - Colorblind-safe palette (avoids red-green confusion)
 * - Never relies on color alone (uses shape + pattern + text)
 * - Neurodivergent-friendly (consistent, predictable, minimal clutter)
 * - Scalable for all screen sizes
 */

// Zone colors designed to be distinguishable for all color vision types
// Using varied luminance + hue to ensure separation even in grayscale
object ZoneColors {
    // Baseline palette (WCAG-considered, varied luminance)
    private val base = listOf(
        Color(0xFFE8F4F8), Color(0xFFFFF3E0), Color(0xFFE8EAF6), Color(0xFFF3E5F5),
        Color(0xFFE0F2F1), Color(0xFFFCE4EC), Color(0xFFFFF8E1), Color(0xFFE3F2FD), Color(0xFFEFEBE9)
    )
    private val high = listOf(
        Color(0xFFB2EBF2), Color(0xFFFFCC80), Color(0xFFC5CAE9), Color(0xFFCE93D8),
        Color(0xFF80CBC4), Color(0xFFF48FB1), Color(0xFFFFE082), Color(0xFF90CAF9), Color(0xFFBCAAA4)
    )

    // Colorblind palettes synthesized to preserve luminance ordering and reduce confusions
    private val deuteranopia = listOf(
        Color(0xFFE8F4F8), Color(0xFFFFF3E0), Color(0xFFE8EAF6), Color(0xFFF3E5F5),
        Color(0xFFE0F2F1), Color(0xFFFDEFEF), Color(0xFFFFFAE6), Color(0xFFE6F0FB), Color(0xFFF0EEEC)
    )
    private val protanopia = listOf(
        Color(0xFFE6F6FA), Color(0xFFFFF5E6), Color(0xFFE9ECF7), Color(0xFFF2E6F7),
        Color(0xFFDFF3F1), Color(0xFFF8E7EE), Color(0xFFFFF9E3), Color(0xFFE4F1FC), Color(0xFFEEECEA)
    )
    private val tritanopia = listOf(
        Color(0xFFF0F5E8), Color(0xFFFFF3E0), Color(0xFFEDE9E0), Color(0xFFF3E5F5),
        Color(0xFFE0EFEF), Color(0xFFFDEDEA), Color(0xFFFFF8E1), Color(0xFFEAEAEA), Color(0xFFEFE7E4)
    )
    private val tetartanopia = listOf(
        // Hypothetical fourth cone deficiency approximation: reduce blue/yellow confusions
        Color(0xFFEDEFEF), Color(0xFFFFF3E0), Color(0xFFE8EAF0), Color(0xFFF2E6F0),
        Color(0xFFE0F0EE), Color(0xFFF8E8EE), Color(0xFFFFF8E6), Color(0xFFE6EEF4), Color(0xFFEEECE9)
    )
    private val achromatopsia = listOf(
        // Grayscale with varied luminance; WCAG-compliant contrasts
        Color(0xFFF5F5F5), Color(0xFFEDEDED), Color(0xFFE6E6E6), Color(0xFFDDDDDD),
        Color(0xFFD5D5D5), Color(0xFFCDCDCD), Color(0xFFC5C5C5), Color(0xFFBDBDBD), Color(0xFFB5B5B5)
    )

    enum class Palette { BASE, HIGH, DEUTERANOPIA, PROTANOPIA, TRITANOPIA, TETARTANOPIA, ACHROMATOPSIA }

    fun forZone(zoneId: Int, highContrast: Boolean = false, palette: Palette = Palette.BASE): Color {
        val colors = when {
            highContrast -> high
            palette == Palette.DEUTERANOPIA -> deuteranopia
            palette == Palette.PROTANOPIA -> protanopia
            palette == Palette.TRITANOPIA -> tritanopia
            palette == Palette.TETARTANOPIA -> tetartanopia
            palette == Palette.ACHROMATOPSIA -> achromatopsia
            else -> base
        }
        return colors[zoneId % colors.size]
    }
}

// Semantic colors - designed for WCAG AA compliance
data class GameColors(
    // Backgrounds
    val surface: Color = Color(0xFFFAFAFA),
    val surfaceDim: Color = Color(0xFFF5F5F5),

    // Primary actions - purple theme consistent with menu
    val primary: Color = Color(0xFF5E35B1),        // Contrast 7.2:1 on white
    val primaryContainer: Color = Color(0xFFEDE7F6),
    val onPrimary: Color = Color.White,

    // Selection state - distinct from zone colors
    val selected: Color = Color(0xFFD1C4E9),       // Light purple, obvious selection
    val selectedBorder: Color = Color(0xFF5E35B1), // Thick border for non-color indicator

    // Text - all meet 4.5:1 minimum on their backgrounds
    val textPrimary: Color = Color(0xFF1A1A1A),    // Near-black, 15.5:1 contrast
    val textSecondary: Color = Color(0xFF424242),  // Dark gray, 9.7:1 contrast
    val textHint: Color = Color(0xFF757575),       // Medium gray, 4.6:1 contrast

    // Borders - cage borders use shape, not just color
    val borderThick: Color = Color(0xFF212121),    // Near-black for cage boundaries
    val borderThin: Color = Color(0xFFBDBDBD),     // Light gray for grid lines

    // Feedback colors - use icons/shapes alongside
    val success: Color = Color(0xFF2E7D32),        // Green with icon
    val error: Color = Color(0xFFC62828),          // Red with icon
    val warning: Color = Color(0xFFF57C00),        // Orange with icon

    // Notes and hints
    val noteText: Color = Color(0xFF1565C0),       // Blue, distinct from main text
    val hintText: Color = Color(0xFF7B1FA2),       // Purple for AI hints

    // Buttons
    val buttonPrimary: Color = Color(0xFF5E35B1),
    val buttonSecondary: Color = Color(0xFFE0E0E0),
    val buttonText: Color = Color(0xFF212121)
)

// Dark theme for reduced eye strain
val DarkGameColors = GameColors(
    surface = Color(0xFF121212),
    surfaceDim = Color(0xFF1E1E1E),
    primary = Color(0xFFB39DDB),
    primaryContainer = Color(0xFF311B92),
    onPrimary = Color(0xFF121212),
    selected = Color(0xFF4527A0),
    selectedBorder = Color(0xFFB39DDB),
    textPrimary = Color(0xFFE0E0E0),
    textSecondary = Color(0xFFBDBDBD),
    textHint = Color(0xFF9E9E9E),
    borderThick = Color(0xFFE0E0E0),
    borderThin = Color(0xFF424242),
    success = Color(0xFF81C784),
    error = Color(0xFFE57373),
    warning = Color(0xFFFFB74D),
    noteText = Color(0xFF64B5F6),
    hintText = Color(0xFFCE93D8),
    buttonPrimary = Color(0xFFB39DDB),
    buttonSecondary = Color(0xFF424242),
    buttonText = Color(0xFFE0E0E0)
)

// Responsive dimensions that scale with screen size
data class GameDimensions(
    // Cell dimensions
    val cellMinSize: Dp = 40.dp,
    val cellPadding: Dp = 4.dp,

    // Border widths - thick borders for cages provide non-color differentiation
    val cageBorderWidth: Dp = 3.dp,
    val gridBorderWidth: Dp = 1.dp,

    // Text sizes - scalable
    val clueTextSize: TextUnit = 11.sp,
    val valueTextSize: TextUnit = 22.sp,
    val noteTextSize: TextUnit = 9.sp,
    val buttonTextSize: TextUnit = 20.sp,

    // Touch targets - WCAG minimum 44dp, we use 48dp+
    val buttonMinSize: Dp = 52.dp,
    val touchTargetMin: Dp = 48.dp,

    // Spacing
    val gridPadding: Dp = 8.dp,
    val controlSpacing: Dp = 12.dp,

    // === Alignment & Positioning (ratio-based for adaptive scaling) ===

    // Cage clue box - depth perception enhancement
    val clueBoxElevation: Dp = 2.dp,              // Shadow depth for 3D effect
    val clueBoxCornerRadius: Dp = 3.dp,           // Slightly rounded corners
    val clueBoxPaddingHorizontal: Dp = 3.dp,      // Inner horizontal padding
    val clueBoxPaddingVertical: Dp = 1.dp,        // Inner vertical padding

    // Value number positioning (ratios of cell height for proportional scaling)
    val valueVerticalOffsetRatio: Float = 0.10f,  // Offset when clue present (10% of cell height)

    // Notes/hints grid sizing (ratios of cell size)
    val noteBoxSizeRatio: Float = 0.28f,          // Each note box = 28% of cell width (for 3x3 grid)
    val noteGridOffsetRatio: Float = 0.15f,       // Vertical offset when clue present (15% of cell height)
    val hintGridOffsetRatio: Float = 0.18f        // Slightly larger offset for hints (18% of cell height)
)

// Large screen / tablet dimensions
val LargeGameDimensions = GameDimensions(
    cellMinSize = 56.dp,
    cellPadding = 6.dp,
    cageBorderWidth = 4.dp,
    gridBorderWidth = 1.dp,
    clueTextSize = 14.sp,
    valueTextSize = 28.sp,
    noteTextSize = 11.sp,
    buttonTextSize = 24.sp,
    buttonMinSize = 64.dp,
    touchTargetMin = 56.dp,
    gridPadding = 16.dp,
    controlSpacing = 16.dp,
    // Large screen alignment tokens
    clueBoxElevation = 3.dp,          // Slightly more depth on larger screens
    clueBoxCornerRadius = 4.dp,
    clueBoxPaddingHorizontal = 4.dp,
    clueBoxPaddingVertical = 2.dp,
    valueVerticalOffsetRatio = 0.08f, // Slightly less offset ratio (cells are bigger)
    noteBoxSizeRatio = 0.26f,         // Slightly smaller ratio (more room)
    noteGridOffsetRatio = 0.12f,
    hintGridOffsetRatio = 0.15f
)

// Extension function for responsive button sizing
fun GameDimensions.getResponsiveButtonSize(
    puzzleSize: Int,
    screenWidth: Dp
): Dp {
    // Determine max buttons per row based on puzzle size
    val maxButtonsPerRow = when {
        puzzleSize <= 5 -> puzzleSize
        else -> 5
    }

    // Calculate available width
    val totalSpacing = controlSpacing * (maxButtonsPerRow - 1)
    val horizontalPadding = gridPadding * 2
    val availableWidth = screenWidth - totalSpacing - horizontalPadding

    // Calculate size that fits in available space
    val calculatedSize = availableWidth / maxButtonsPerRow

    // Constrain to WCAG minimum (44dp) and maximum (buttonMinSize)
    return calculatedSize.coerceIn(44.dp, buttonMinSize)
}

// Accessibility settings
data class AccessibilitySettings(
    val highContrastMode: Boolean = false,
    val reduceMotion: Boolean = false,
    val largeText: Boolean = false,
    val showZonePatterns: Boolean = false,  // Adds patterns to zones for colorblind users
    val hapticFeedback: Boolean = true
)

// Composition locals for theme access
val LocalGameColors = staticCompositionLocalOf { GameColors() }
val LocalGameDimensions = staticCompositionLocalOf { GameDimensions() }
val LocalAccessibilitySettings = staticCompositionLocalOf { AccessibilitySettings() }

@Composable
fun GameTheme(
    darkTheme: Boolean = false,
    largeScreen: Boolean = false,
    accessibilitySettings: AccessibilitySettings = AccessibilitySettings(),
    content: @Composable () -> Unit
) {
    val colors = if (darkTheme) DarkGameColors else GameColors()
    val dimensions = if (largeScreen) LargeGameDimensions else GameDimensions()

    CompositionLocalProvider(
        LocalGameColors provides colors,
        LocalGameDimensions provides dimensions,
        LocalAccessibilitySettings provides accessibilitySettings
    ) {
        content()
    }
}
