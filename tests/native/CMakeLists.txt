# CMakeLists.txt for standalone native test harness
#
# Builds puzzle generation code for host testing with coverage instrumentation.
# Usage:
#   mkdir build && cd build
#   cmake -DCMAKE_BUILD_TYPE=Debug ..
#   make
#   ./keen_test_harness
#   make coverage  # Generate HTML coverage report

cmake_minimum_required(VERSION 3.16)
project(KeenTestHarness C)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Source directory
set(JNI_DIR "${CMAKE_SOURCE_DIR}/../../app/src/main/jni")

# Coverage flags
set(COVERAGE_FLAGS "-fprofile-arcs -ftest-coverage")
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} ${COVERAGE_FLAGS} -O0 -g")
set(CMAKE_EXE_LINKER_FLAGS_DEBUG "${CMAKE_EXE_LINKER_FLAGS_DEBUG} ${COVERAGE_FLAGS}")

# Warnings (match project standards)
add_compile_options(
    -Wall -Wextra -Wpedantic
    -Wno-unused-parameter
    -Wno-sign-compare
    -Wno-missing-field-initializers
)

# Core puzzle sources (exclude Android JNI wrapper)
set(PUZZLE_SOURCES
    ${JNI_DIR}/keen.c
    ${JNI_DIR}/keen_generate.c
    ${JNI_DIR}/keen_solver.c
    ${JNI_DIR}/keen_hints.c
    ${JNI_DIR}/keen_validate.c
    ${JNI_DIR}/latin.c
    ${JNI_DIR}/random.c
    ${JNI_DIR}/tree234.c
    ${JNI_DIR}/dsf.c
    ${JNI_DIR}/malloc.c
    ${JNI_DIR}/dlx.c
    ${JNI_DIR}/maxflow_optimized.c
)

# Test harness executable
add_executable(keen_test_harness
    keen_test_harness.c
    host_stubs.c
    ${PUZZLE_SOURCES}
)

target_include_directories(keen_test_harness PRIVATE ${JNI_DIR})

# Enable math library
target_link_libraries(keen_test_harness m gcov)

# Coverage report target
add_custom_target(coverage
    COMMAND lcov --capture --directory . --output-file coverage.info --ignore-errors mismatch
    COMMAND lcov --remove coverage.info '/usr/*' --output-file coverage.info
    COMMAND genhtml coverage.info --output-directory coverage_report
    COMMAND echo "Coverage report: ${CMAKE_BINARY_DIR}/coverage_report/index.html"
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    DEPENDS keen_test_harness
    COMMENT "Generating coverage report"
)

# Clean coverage data
add_custom_target(coverage_clean
    COMMAND find . -name "*.gcda" -delete
    COMMAND find . -name "*.gcno" -delete
    COMMAND rm -rf coverage.info coverage_report
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Cleaning coverage data"
)
