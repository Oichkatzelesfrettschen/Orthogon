import re

def fix_validate(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Ensure target and op are long
    content = re.sub(r'unsigned\s+long\s+(target|op)\s*=', r'long \1 =', content)
    
    # 2. Fix the bitwise extraction logic to be explicit and signed result
    content = re.sub(r'long\s+target\s*=\s*\(long\)\(uclue\s*&\s*~CMASK\);', 
                     r'long target = (long)((unsigned long)uclue & ~CMASK);', content)
    content = re.sub(r'long\s+op\s*=\s*\(long\)\(uclue\s*&\s*CMASK\);', 
                     r'long op = (long)((unsigned long)uclue & CMASK);', content)

    # 3. Change intermediate calculation types back to long
    content = re.sub(r'unsigned\s+long\s+(sum|prod|pow_ab|pow_ba|g|l|x)\s*=', r'long \1 =', content)
    
    # 4. Remove redundant casts in comparisons
    content = re.sub(r'return\s+\(unsigned\s+long\)(sum|prod|g|l|x)\s*==\s*target;', r'return \1 == target;', content)
    content = re.sub(r'return\s+target\s*==\s*\(unsigned\s+long\)labs', r'return target == labs', content)
    content = re.sub(r'pow_ab\s*<=\s*target', r'pow_ab <= target', content)
    content = re.sub(r'pow_ba\s*<=\s*target', r'pow_ba <= target', content)
    content = re.sub(r'pow_ab\s*==\s*target', r'pow_ab == target', content)
    content = re.sub(r'pow_ba\s*==\s*target', r'pow_ba == target', content)
    content = re.sub(r'\(unsigned\s+long\)\(a\s*/\s*b\)\s*==\s*target', r'(a / b) == target', content)
    content = re.sub(r'a\s*/\s*\(unsigned\s+long\)b\s*==\s*target', r'(a / b) == target', content)

    # 5. Fix loops
    content = re.sub(r'pow_ab\s*\*\s*=\s*\(unsigned\s+long\)a', r'pow_ab *= a', content)
    content = re.sub(r'pow_ba\s*\*\s*=\s*\(unsigned\s+long\)b', r'pow_ba *= b', content)

    with open(path, 'w') as f:
        f.write(content)

def fix_keen(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Ensure value and op are long
    content = re.sub(r'unsigned\s+long\s+(value|op)\s*=', r'long \1 =', content)
    content = re.sub(r'long\s+value\s*=\s*uclue\s*&\s*~CMASK;', r'long value = (long)((unsigned long)uclue & ~CMASK);', content)
    content = re.sub(r'long\s+op\s*=\s*uclue\s*&\s*CMASK;', r'long op = (long)((unsigned long)uclue & CMASK);', content)

    # Arithmetic promotion fixes
    content = re.sub(r'\(unsigned\s+long\)i\s*([+*])\s*\(unsigned\s+long\)value', r'(long)((unsigned long)i \1 (unsigned long)value)', content)
    content = re.sub(r'\(unsigned\s+long\)total\s*%\s*\(unsigned\s+long\)value', r'(long)((unsigned long)total % (unsigned long)value)', content)
    content = re.sub(r'\(unsigned\s+long\)j\s*%\s*\(unsigned\s+long\)value', r'(long)((unsigned long)j % (unsigned long)value)', content)
    content = re.sub(r'\(unsigned\s+long\)value\s*%\s*\(unsigned\s+long\)j', r'(long)((unsigned long)value % (unsigned long)j)', content)

    # Comparisons
    content = re.sub(r'\(unsigned\s+long\)value\s*>=\s*\(unsigned\s+long\)i', r'value >= (long)i', content)
    content = re.sub(r'\(unsigned\s+long\)\(j\s*%\s*i\)\s*==\s*\(unsigned\s+long\)value', r'(long)(j % i) == value', content)
    content = re.sub(r'\(unsigned\s+long\)\(j\s*%\s*i\)\s*!=\s*\(unsigned\s+long\)value', r'(long)(j % i) != value', content)
    content = re.sub(r'\(unsigned\s+long\)total\s*==\s*\(unsigned\s+long\)value', r'total == (int)value', content)
    
    # GCD/LCM comparisons
    content = re.sub(r'==\s*\(long\)value', r'== value', content)
    content = re.sub(r'result\s*>\s*\(long\)value', r'result > value', content)
    content = re.sub(r'result\s*!=\s*\(long\)value', r'result != value', content)

    with open(path, 'w') as f:
        f.write(content)

fix_validate('app/src/main/jni/keen_validate.c')
fix_keen('app/src/main/jni/keen.c')
