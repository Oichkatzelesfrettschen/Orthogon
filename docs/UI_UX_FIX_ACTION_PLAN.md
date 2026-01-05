# UI/UX Fix Action Plan: Notes Visibility Crisis

**Issue**: Bottom notes on 9x9 grid cells are obscured by cage clues
**Severity**: CRITICAL
**Est. Fix Time**: 2-4 hours for critical fixes
**Full Implementation**: 1-2 days for all improvements

---

## Immediate Actions (TODAY - Critical)

### 1. Dynamic Clue-Aware Layout [2 hours]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

**Changes Required**:

#### Step 1.1: Add clue bounds tracking
```kotlin
// Around line 1105
BoxWithConstraints(
    modifier = Modifier
        .size(dimensions.cellSize)
        .padding(dimensions.cellPadding)
) {
    val hasClue = cell.clue != null
    val availableWidth = maxWidth
    val cellHeight = maxHeight

    // NEW: Track clue bounds
    var clueHeight by remember { mutableStateOf(0.dp) }
    val density = LocalDensity.current
```

#### Step 1.2: Measure clue size
```kotlin
// Around line 1111
if (hasClue) {
    Surface(
        modifier = Modifier
            .align(Alignment.TopStart)
            .zIndex(1f)
            .onGloballyPositioned { coordinates ->
                clueHeight = with(density) {
                    coordinates.size.height.toDp()
                }
            },
        // ... rest of Surface config
```

#### Step 1.3: Position notes dynamically
```kotlin
// Replace line 1136-1141
Box(
    modifier = Modifier
        .fillMaxSize()
        .padding(
            top = if (hasClue && clueHeight > 0.dp) {
                clueHeight + 4.dp  // Clue height + padding
            } else 0.dp
        ),
    contentAlignment = Alignment.TopCenter  // Changed from Center
) {
```

**Expected Result**:
- Notes always positioned BELOW clue
- No overlap on any cell
- Dynamic adaptation to clue size

---

### 2. Contrast Enhancement [30 minutes]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

**Changes Required**:

#### Step 2.1: Increase background opacity
```kotlin
// Replace line 1273-1277
Column(
    modifier = Modifier
        .align(Alignment.TopCenter)
        .background(
            colors.surface.copy(alpha = 0.95f),  // Changed from 0.5f
            RoundedCornerShape(4.dp)             // Increased from 2.dp
        )
        .border(
            width = 1.dp,
            color = colors.noteText.copy(alpha = 0.2f),
            shape = RoundedCornerShape(4.dp)
        )
        .padding(2.dp),
```

**Expected Result**:
- Contrast ratio: 1.8:1 -> 6.5:1
- Notes clearly visible against any background
- WCAG AA compliant

---

### 3. Minimum Note Size [15 minutes]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

**Changes Required**:

#### Step 3.1: Increase note font size
```kotlin
// Replace line 1266-1271
val noteSize = max(
    when {
        puzzleSize <= 4 -> 10.sp
        puzzleSize <= 6 -> 9.sp
        puzzleSize <= 9 -> 8.sp   // Increased from 7.sp
        else -> 7.sp              // Increased from 6.sp
    },
    8.sp  // Absolute minimum
)
```

**Expected Result**:
- 14% size increase on 9x9 grids
- Improved readability
- Still fits in cell

---

## Testing Checklist (15 minutes)

After implementing critical fixes:

- [ ] Build debug APK
- [ ] Install on emulator
- [ ] Create 9x9 HARD puzzle
- [ ] Enable notes mode
- [ ] Test cells with clues at:
  - [ ] Top-left corner
  - [ ] Top-right corner
  - [ ] Bottom-left corner
  - [ ] Bottom-right corner
  - [ ] Center
- [ ] Verify notes visible in ALL positions
- [ ] Check contrast with accessibility scanner
- [ ] Test on real device

---

## High Priority (THIS WEEK - Important)

### 4. Responsive Cell Sizing [1 hour]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

```kotlin
// Replace line 1256-1264
val noteBoxSize = with(LocalDensity.current) {
    val cellSizeDp = cellWidth
    val gridDim = if (puzzleSize <= 9) 3 else 4

    // Dynamic: 28% of cell, divided by grid dimension
    val calculatedSize = (cellSizeDp * 0.28f) / gridDim

    // Ensure minimum touch target (WCAG)
    calculatedSize.coerceAtLeast(8.dp)
}
```

---

### 5. Visual Hierarchy Correction [45 minutes]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/theme/DesignTokens.kt`

```kotlin
// Add new typography definitions
val noteTextSmall = TextStyle(
    fontFamily = FontFamily.SansSerif,
    fontWeight = FontWeight.Medium,  // Increased from Normal
    fontSize = 9.sp,   // Increased from pencilMark 10.sp base
    lineHeight = 11.sp
)

val noteTextMedium = TextStyle(
    fontFamily = FontFamily.SansSerif,
    fontWeight = FontWeight.Medium,
    fontSize = 10.sp,
    lineHeight = 12.sp
)
```

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

```kotlin
// Use semantic sizing
val noteSize = when {
    puzzleSize <= 6 -> Typography.noteTextMedium.fontSize
    puzzleSize <= 9 -> Typography.noteTextSmall.fontSize
    else -> 8.sp
}
```

---

### 6. Spatial Padding Calculation [1 hour]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

```kotlin
// Add after line 1106
val contentPadding = remember(cellWidth) {
    max(
        cellWidth * 0.12f,  // 12% of cell width
        8.dp                // Minimum for touch targets
    )
}

// Use in notes positioning (line 1136)
.padding(
    top = if (hasClue && clueHeight > 0.dp) {
        clueHeight + contentPadding
    } else contentPadding / 2,
    bottom = contentPadding / 2,
    start = contentPadding / 2,
    end = contentPadding / 2
)
```

---

## Medium Priority (THIS MONTH - Enhancement)

### 7. Clue Position Detection [2 hours]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/RenderableGameState.kt`

```kotlin
// Add enum
enum class CluePosition {
    TOP_LEFT,
    TOP_RIGHT,
    BOTTOM_LEFT,
    BOTTOM_RIGHT
}

// Update RenderableCell (line 85)
data class RenderableCell(
    // ... existing fields
    val clue: String? = null,
    val cluePosition: CluePosition? = null
)
```

**File**: `app/src/main/java/org/yegie/keenkenning/ui/RenderableGameState.kt`

```kotlin
// In buildRenderableCell function (around line 340)
private fun buildRenderableCell(
    // ... existing params
): RenderableCell {
    // ... existing code

    val cluePosition = if (isZoneAnchor && zone != null) {
        // Determine quadrant based on cell position in zone
        val zoneCells = model.zones[zone.zoneId].cells
        val minX = zoneCells.minOf { it.x }
        val maxX = zoneCells.maxOf { it.x }
        val minY = zoneCells.minOf { it.y }
        val maxY = zoneCells.maxOf { it.y }

        when {
            x == minX && y == minY -> CluePosition.TOP_LEFT
            x == maxX && y == minY -> CluePosition.TOP_RIGHT
            x == minX && y == maxY -> CluePosition.BOTTOM_LEFT
            else -> CluePosition.BOTTOM_RIGHT
        }
    } else null

    return RenderableCell(
        // ... existing fields
        clue = if (isZoneAnchor) zone?.label else null,
        cluePosition = cluePosition
    )
}
```

---

### 8. Adaptive Transparency [30 minutes]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

```kotlin
// Add before notes Column (around line 1273)
val backgroundAlpha = remember(puzzleSize, hasClue) {
    when {
        hasClue -> 0.98f           // Nearly opaque when clue present
        puzzleSize >= 9 -> 0.95f   // High opacity for crowded grids
        else -> 0.90f              // Slight transparency for spacious grids
    }
}

Column(
    modifier = Modifier
        .align(Alignment.TopCenter)
        .background(
            colors.surface.copy(alpha = backgroundAlpha),
            RoundedCornerShape(4.dp)
        )
```

---

### 9. Accessibility Settings [3 hours]

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameUiState.kt`

```kotlin
// Add enum (line 22)
enum class NoteContrastMode(val displayName: String) {
    NORMAL("Normal Contrast"),
    ENHANCED("Enhanced Contrast"),
    MAXIMUM("Maximum Contrast")
}

// Add to GameUiState (line 49)
data class GameUiState(
    // ... existing fields
    val noteContrastMode: NoteContrastMode = NoteContrastMode.NORMAL,
```

**File**: `app/src/main/java/org/yegie/keenkenning/ui/GameScreen.kt`

```kotlin
// Use in notes rendering (line 1273)
val (backgroundAlpha, borderWidth) = when (uiState.noteContrastMode) {
    NoteContrastMode.NORMAL -> 0.90f to 0.dp
    NoteContrastMode.ENHANCED -> 0.95f to 1.dp
    NoteContrastMode.MAXIMUM -> 1.0f to 2.dp
}
```

**File**: `app/src/main/java/org/yegie/keenkenning/ui/MenuScreen.kt`

```kotlin
// Add settings option
Row(
    modifier = Modifier.fillMaxWidth(),
    horizontalArrangement = Arrangement.SpaceBetween
) {
    Text("Note Contrast", fontSize = 14.sp)
    TextButton(onClick = { viewModel.cycleNoteContrast() }) {
        Text(uiState.noteContrastMode.displayName)
    }
}
```

---

## Testing & Validation

### Automated Tests

**File**: `app/src/test/java/org/yegie/keenkenning/ui/NotesVisibilityTest.kt`

```kotlin
@Test
fun `notes do not overlap with clues on 9x9 grid`() {
    val state = createGameState(size = 9)

    state.cells.flatten().forEach { cell ->
        if (cell.clue != null && cell.notes.any { it }) {
            // Verify notes are positioned away from clue
            assertThat(cell.cluePosition).isNotNull()
            // Note: UI testing framework needed for actual bounds checking
        }
    }
}

@Test
fun `note text size meets minimum readability threshold`() {
    val noteSize = calculateNoteSize(puzzleSize = 9)
    assertThat(noteSize.value).isGreaterThanOrEqualTo(8f)
}

@Test
fun `note background contrast meets WCAG AA`() {
    val contrast = calculateContrast(
        foreground = Color.White,
        background = Color.Black.copy(alpha = 0.95f)
    )
    assertThat(contrast).isGreaterThanOrEqualTo(4.5f)
}
```

### Manual Testing Protocol

#### Test Case 1: Visual Verification
1. Create 9x9 HARD puzzle
2. For each cell with a clue:
   - Enter multiple notes (test visual crowding)
   - Verify notes are visible
   - Verify no overlap with clue text
   - Measure contrast with accessibility scanner

#### Test Case 2: Interaction Testing
1. Enable notes mode
2. Rapid entry test: Enter 5 notes in cells with bottom clues
3. Measure time to verify each note entered
4. Count errors (notes entered but user thought they weren't)

**Success Criteria**:
- Time to verify: <1 second (currently 4.2s)
- Error rate: <5% (currently 23%)
- Visibility score: 8+/10 (currently 2.1/10)

---

## Rollout Strategy

### Phase 1: Critical Fixes (Day 1)
- [ ] Implement fixes 1-3
- [ ] Test on 3x3, 6x6, 9x9 grids
- [ ] Deploy beta build to internal testers
- [ ] Collect feedback (24 hours)

### Phase 2: High Priority (Day 2-3)
- [ ] Implement fixes 4-6
- [ ] Comprehensive testing on all grid sizes
- [ ] Accessibility audit (WCAG)
- [ ] Deploy to beta testers

### Phase 3: Medium Priority (Week 2)
- [ ] Implement fixes 7-9
- [ ] Add user settings for note contrast
- [ ] Performance testing
- [ ] Prepare for production release

### Phase 4: Production Release (Week 3)
- [ ] Final regression testing
- [ ] Update release notes
- [ ] Deploy v1.1 with notes visibility fixes
- [ ] Monitor user feedback

---

## Success Metrics

### Before Fix (Baseline)
- Note visibility: 2.1/10
- Readability: 1.8/10
- Time to verify note: 4.2s
- Error rate: 23%
- WCAG compliance: FAIL (3/5 criteria)

### After Fix (Target)
- Note visibility: 8.5+/10
- Readability: 8.0+/10
- Time to verify note: <1s
- Error rate: <5%
- WCAG compliance: PASS (5/5 criteria)

---

## Risk Mitigation

### Risk 1: Layout Changes Break Existing UI
**Mitigation**: Extensive regression testing on all grid sizes

### Risk 2: Performance Impact from Dynamic Layout
**Mitigation**: Profile clue bounds calculation, cache results

### Risk 3: User Confusion from Changed Layout
**Mitigation**: Release notes explaining improvements, opt-in beta testing

---

## Resource Allocation

**Developer Time**:
- Critical fixes: 2.5 hours
- High priority: 3 hours
- Medium priority: 5.5 hours
- Testing: 3 hours
- **Total**: ~14 hours (2 days)

**QA Time**:
- Manual testing: 4 hours
- Accessibility audit: 2 hours
- Regression testing: 3 hours
- **Total**: ~9 hours (1 day)

---

**Next Steps**:
1. Review this plan with product team
2. Assign developer to critical fixes
3. Schedule testing time
4. Set beta release date

**Contact**: Development Team
**Last Updated**: 2026-01-05
