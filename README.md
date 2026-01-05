# Keen Classik for Android

A classic KenKen-style logic puzzle game for Android phones and tablets, with Android TV support. Built with Jetpack Compose and powered by native C algorithms.

**Keen Classik** is the stable, production-ready version featuring traditional KenKen puzzles (3x3-9x9 grids) with multiple game modes and difficulty levels.

**Note**: Experimental features including ML assistance and extended grid sizes (10x10-16x16) are currently under development on the `kenning-experimental` branch. This work-in-progress branch, called **Keen Kenning**, adds neural ML hints and additional puzzle variations.

## Download

**[Latest Release](https://github.com/Oichkatzelesfrettschen/KeenKenning/releases)**

| APK | Architecture | Size | Notes |
|-----|--------------|------|-------|
| `app-universal-debug.apk` | All | ~46MB | Works everywhere |
| `app-arm64-v8a-debug.apk` | ARM64 | ~24MB | Modern phones |
| `app-armeabi-v7a-debug.apk` | ARM32 | ~23MB | Older phones |
| `app-x86_64-debug.apk` | x86_64 | ~25MB | Emulators, Chromebooks |
| `app-x86-debug.apk` | x86 | ~25MB | 32-bit x86 |
| `app-riscv64-debug.apk` | RISC-V | ~17MB | Emerging architecture |

## Features (Keen Classik)

### Core Game Modes

| Mode | Description | Status |
|------|-------------|--------|
| **Standard** | All operations (+, -, x, /) | Complete |
| **Multiply** | Multiplication only | Complete |
| **Mystery** | Operations hidden - deduce them! | Complete |

### Grid Sizes
- 3x3, 4x4, 5x5, 6x6, 7x7, 8x8, 9x9

### Difficulty Levels
- Easy
- Normal
- Hard
- Insane
- Ludicrous

### Additional Features
- **Victory Animation**: Bouncing tiles celebration on puzzle completion
- **Save/Load**: Multiple save slots with auto-save
- **Accessibility**: Full TalkBack/screen reader support
- **Android TV**: D-pad navigation with 10-foot UI focus indicators
- **Dark Theme**: Modern dark UI throughout

### Experimental Features (Kenning Branch)
The following features are under active development on the `kenning-experimental` branch:
- Neural ML Hints (ONNX-based solver)
- Extended grid sizes (10x10, 12x12, 16x16)
- Additional game modes (Zero Mode, Powers, Negative, Modular, Killer, Tutorial, Adaptive, Story)
- Quantum Visualization (probability hints)

## Requirements

- Android 5.1+ (API 22)
- ~25MB storage for architecture-specific APK
- ~50MB storage for universal APK

## Building from Source

### Prerequisites
- **JDK 21** (Required by Gradle 8.6+)
- **Android SDK** with API 35 (Compile SDK)
- **Android NDK** 27.x
- **CMake** 3.22.1+ (Enforcing **C11** standard)
- **Memory**: 4GB+ heap recommended for Gradle daemon

### Build Commands
```bash
# Clean build (Recommended for strict mode)
./gradlew clean assembleClassikDebug

# Run Unit Tests (Strict warnings-as-errors)
./gradlew testClassikDebugUnitTest

# Release build
./gradlew assembleClassikRelease
```

> **Note**: This project uses `allWarningsAsErrors = true`. Any code warnings will fail the build to ensure high quality.

Output: `app/build/outputs/apk/classik/debug/`

### Building the Experimental Kenning Flavor
To build the experimental version with ML features:
```bash
./gradlew assembleKenningDebug
```

## Architecture

```
+-------------------------------------------------------------+
|                    Compose UI Layer                         |
|  GameScreen.kt - MenuScreen.kt - VictoryAnimation.kt        |
+-------------------------------------------------------------+
|                   ViewModel Layer                           |
|  GameViewModel.kt - GameUiState.kt - SaveManager.kt         |
+-------------------------------------------------------------+
|                  Integration Layer                          |
|  KeenModelBuilder.java - PuzzleGenerator.kt                 |
+-------------------------------------------------------------+
|                    Native Layer (C)                         |
|  keen.c - keen-android-jni.c (via CMake/NDK)                |
+-------------------------------------------------------------+
```

## Known Issues (Debug Build)

1. **First launch**: Initial puzzle generation may take 1-2 seconds on older devices
2. **Large grids**: 9x9 puzzles with high difficulty may require longer computation time

## Testing Checklist for Debug Testers

- [ ] App installs and launches without crash
- [ ] Menu displays core game modes (Standard, Multiply, Mystery)
- [ ] Can select different grid sizes (3x3 to 9x9)
- [ ] Puzzle generates correctly for each mode
- [ ] Cell input works (tap cell, tap number)
- [ ] Notes mode toggles correctly
- [ ] Undo/Clear functions work
- [ ] Victory animation triggers on correct solution
- [ ] Save/Load functionality works
- [ ] Settings dialog opens
- [ ] Back button returns to menu
- [ ] Screen rotation doesn't crash app
- [ ] TalkBack announces cells and actions

## Credits

- **Core Algorithms**: [Simon Tatham's Portable Puzzle Collection](https://www.chiark.greenend.org.uk/~sgtatham/puzzles/)
- **Original Android Port**: Sergey Maltsev
- **Keen Classik Enhancements**: KeenKenning Contributors

## License

MIT

---

*Debug build - Report issues at [GitHub Issues](https://github.com/Oichkatzelesfrettschen/KeenKenning/issues)*
