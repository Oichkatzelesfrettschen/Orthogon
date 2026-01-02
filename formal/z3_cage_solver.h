/**
 * @file z3_cage_solver.h
 * @brief Z3 SMT solver integration for KenKen cage constraint solving
 *
 * This header provides the interface for using Z3 to solve cage constraints
 * when tuple enumeration exceeds the threshold (>1000 candidates).
 *
 * Part of the DLX+SAT hybrid architecture:
 * - DLX handles exact cover (Latin square structure)
 * - Z3/SAT handles arithmetic cage constraints for large cages
 *
 * @author KeenKenning Project
 * @date 2026-01-01
 * @license MIT
 */

#ifndef Z3_CAGE_SOLVER_H
#define Z3_CAGE_SOLVER_H

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Cage operation types matching keen_modes.h
 */
typedef enum {
    CAGE_OP_ADD = 0,    /**< Addition: sum of cells equals target */
    CAGE_OP_SUB = 1,    /**< Subtraction: |a - b| equals target */
    CAGE_OP_MUL = 2,    /**< Multiplication: product equals target */
    CAGE_OP_DIV = 3,    /**< Division: a/b or b/a equals target */
    CAGE_OP_XOR = 4,    /**< XOR: bitwise XOR equals target (BITWISE mode) */
    CAGE_OP_MOD = 5     /**< Modular: sum mod N equals target (MODULAR mode) */
} CageOp;

/**
 * @brief A cell position in the grid
 */
typedef struct {
    int row;
    int col;
} CellPos;

/**
 * @brief A cage constraint definition
 */
typedef struct {
    CellPos *cells;     /**< Array of cells in this cage */
    int cell_count;     /**< Number of cells */
    CageOp op;          /**< Arithmetic operation */
    int64_t target;     /**< Target value */
    bool killer;        /**< If true, no repeated digits in cage */
} CageConstraint;

/**
 * @brief Solver context handle (opaque)
 */
typedef struct Z3CageSolverCtx Z3CageSolverCtx;

/**
 * @brief Threshold constants for hybrid DLX+SAT decision
 *
 * When tuple enumeration count exceeds these thresholds:
 * - < TUPLE_THRESHOLD_DLX: Use brute-force enumeration
 * - < TUPLE_THRESHOLD_SAT: Use DLX with pruning
 * - < TUPLE_THRESHOLD_ABORT: Use Z3/SAT solver
 * - >= TUPLE_THRESHOLD_ABORT: Regenerate cage configuration
 */
#define TUPLE_THRESHOLD_SMALL 100
#define TUPLE_THRESHOLD_DLX   500
#define TUPLE_THRESHOLD_SAT   1000
#define TUPLE_THRESHOLD_ABORT 2000

/**
 * @brief Calculate max tuples for a cage
 *
 * For a cage of k cells in an NxN grid, max tuples = N^k
 *
 * @param grid_size The grid dimension N
 * @param cage_size The number of cells in the cage
 * @return Maximum possible tuple combinations
 */
static inline int64_t cage_max_tuples(int grid_size, int cage_size) {
    int64_t result = 1;
    for (int i = 0; i < cage_size; i++) {
        result *= grid_size;
    }
    return result;
}

/**
 * @brief Determine which solver to use based on tuple count
 *
 * @param max_tuples From cage_max_tuples()
 * @return 0=enumerate, 1=DLX, 2=SAT, 3=abort
 */
static inline int solver_decision(int64_t max_tuples) {
    if (max_tuples < TUPLE_THRESHOLD_SMALL) return 0;
    if (max_tuples < TUPLE_THRESHOLD_DLX)   return 1;
    if (max_tuples < TUPLE_THRESHOLD_SAT)   return 2;
    return 3; /* abort and regenerate */
}

/* ============================================================================
 * Z3 Solver API (requires linking with libz3)
 * ============================================================================ */

#ifdef KEEN_USE_Z3

#include <z3.h>

/**
 * @brief Create a new Z3 cage solver context
 *
 * @param grid_size The NxN grid dimension
 * @return Solver context or NULL on failure
 */
Z3CageSolverCtx *z3_cage_solver_new(int grid_size);

/**
 * @brief Free solver context
 */
void z3_cage_solver_free(Z3CageSolverCtx *ctx);

/**
 * @brief Add Latin square constraints to the solver
 *
 * Asserts:
 * - All cells have values in [1, N]
 * - Each row has distinct values
 * - Each column has distinct values
 *
 * @param ctx Solver context
 * @return true on success
 */
bool z3_add_latin_constraints(Z3CageSolverCtx *ctx);

/**
 * @brief Add a cage constraint
 *
 * @param ctx Solver context
 * @param cage The cage definition
 * @return true on success
 */
bool z3_add_cage_constraint(Z3CageSolverCtx *ctx, const CageConstraint *cage);

/**
 * @brief Add a fixed cell value (given clue)
 *
 * @param ctx Solver context
 * @param row Cell row
 * @param col Cell column
 * @param value Fixed value
 * @return true on success
 */
bool z3_add_fixed_cell(Z3CageSolverCtx *ctx, int row, int col, int value);

/**
 * @brief Check satisfiability
 *
 * @param ctx Solver context
 * @return true if satisfiable
 */
bool z3_check_sat(Z3CageSolverCtx *ctx);

/**
 * @brief Get cell value from model
 *
 * Only valid after z3_check_sat() returns true.
 *
 * @param ctx Solver context
 * @param row Cell row
 * @param col Cell column
 * @return Cell value (1 to N) or -1 on error
 */
int z3_get_cell_value(Z3CageSolverCtx *ctx, int row, int col);

/**
 * @brief Get full grid solution
 *
 * Only valid after z3_check_sat() returns true.
 *
 * @param ctx Solver context
 * @param grid Output array of size N*N (row-major)
 * @return true on success
 */
bool z3_get_solution(Z3CageSolverCtx *ctx, int *grid);

/**
 * @brief Check if puzzle has unique solution
 *
 * Finds first solution, adds its negation, checks for second solution.
 *
 * @param ctx Solver context
 * @return true if exactly one solution exists
 */
bool z3_has_unique_solution(Z3CageSolverCtx *ctx);

#endif /* KEEN_USE_Z3 */

/* ============================================================================
 * Fallback: Pure SAT encoding (CNF for external SAT solver)
 * ============================================================================ */

/**
 * @brief Generate CNF clauses for cage constraints
 *
 * Outputs DIMACS CNF format for use with external SAT solvers
 * (kissat, minisat, glucose, etc.)
 *
 * Variable encoding for NxN grid:
 * - Variables 1..N*N*N represent: cell(r,c) = v
 * - Variable number = r*N*N + c*N + (v-1) + 1
 *
 * @param grid_size The NxN dimension
 * @param cages Array of cage constraints
 * @param cage_count Number of cages
 * @param output File pointer for CNF output
 * @return Number of clauses written, or -1 on error
 */
int generate_cnf_clauses(int grid_size,
                         const CageConstraint *cages,
                         int cage_count,
                         void *output /* FILE* */);

/**
 * @brief Convert SAT solution back to grid
 *
 * @param grid_size The NxN dimension
 * @param sat_solution Array of literals (positive = true, negative = false)
 * @param num_literals Number of literals
 * @param grid Output array of size N*N
 * @return true on success
 */
bool sat_to_grid(int grid_size,
                 const int *sat_solution,
                 int num_literals,
                 int *grid);

#ifdef __cplusplus
}
#endif

#endif /* Z3_CAGE_SOLVER_H */
