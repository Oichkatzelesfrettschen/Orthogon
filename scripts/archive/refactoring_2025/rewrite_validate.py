import re

def fix_validate(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Rewrite check_cage_constraint entirely for clarity and correctness
    new_func = """static int check_cage_constraint(const validate_ctx* ctx, int root, digit* values, int ncells) {
    clue_t uclue = ctx->clues[root];
    long target = (long)(uclue & ~CMASK);
    long op = (long)(uclue & CMASK);
    int i;

    /*
     * Killer mode: reject if any digits are repeated in the cage
     */
    if (HAS_MODE(ctx->mode_flags, MODE_KILLER)) {
        int seen = 0;
        for (i = 0; i < ncells; i++) {
            int bit = 1 << values[i];
            if (seen & bit) return 0; /* Duplicate in cage */
            seen |= bit;
        }
    }

    switch (op) {
        case C_ADD: {
            long sum = 0;
            for (i = 0; i < ncells; i++) sum += (long)values[i];
            return sum == target;
        }

        case C_MUL: {
            long prod = 1;
            for (i = 0; i < ncells; i++) prod *= (long)values[i];
            return prod == target;
        }

        case C_SUB: {
            /* 2-cell only: |a-b| = target */
            if (ncells != 2) return 0;
            return target == labs((long)values[0] - (long)values[1]);
        }

        case C_DIV: {
            /* 2-cell only: max/min = target (exact division) */
            if (ncells != 2) return 0;
            long a = (long)values[0], b = (long)values[1];
            if (a < b) {
                long t = a;
                a = b;
                b = t;
            }
            if (b == 0) return 0;
            return (a % b == 0) && (a / b == target);
        }

        case C_EXP: {
            /* 2-cell only: a^b = target or b^a = target */
            if (ncells != 2) return 0;
            long a = (long)values[0], b = (long)values[1];
            long pow_ab = 1, pow_ba = 1;
            for (i = 0; i < b && pow_ab <= target; i++) pow_ab *= a;
            for (i = 0; i < a && pow_ba <= target; i++) pow_ba *= b;
            return pow_ab == target || pow_ba == target;
        }

        case C_MOD: {
            /* 2-cell only: larger % smaller = target */
            if (ncells != 2) return 0;
            long a = (long)values[0], b = (long)values[1];
            if (a < b) {
                long t = a;
                a = b;
                b = t;
            }
            if (b == 0) return 0;
            return (a % b) == target;
        }

        case C_GCD: {
            /* GCD of all digits = target */
            long g = (long)values[0];
            for (i = 1; i < ncells; i++) g = gcd(g, (long)values[i]);
            return g == target;
        }

        case C_LCM: {
            /* LCM of all digits = target */
            long l = (long)values[0];
            for (i = 1; i < ncells; i++) {
                l = lcm(l, (long)values[i]);
                if (l > 10000000) return 0; /* Overflow protection */
            }
            return l == target;
        }

        case C_XOR: {
            /* XOR of all digits = target */
            long x = (long)values[0];
            for (i = 1; i < ncells; i++) x ^= (long)values[i];
            return x == target;
        }

        default:
            return 1; /* Unknown op - assume valid */
    }
}"""
    
    # Replace the whole function
    pattern = r'static int check_cage_constraint\(.*?\)\s*\{.*?^\}'
    content = re.sub(pattern, new_func, content, flags=re.DOTALL | re.MULTILINE)
    
    with open(path, 'w') as f:
        f.write(content)

fix_validate('app/src/main/jni/keen_validate.c')
