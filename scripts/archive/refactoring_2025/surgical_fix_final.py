import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Fix value/target extraction
    # Matches: long value = (long)(uclue & ~CMASK); or similar variants
    # We want: long value = (long)((unsigned long)uclue & ~(unsigned long)CMASK);
    
    # First, simplify existing broken attempts
    content = re.sub(r'\(long\)\(uclue\s*&\s*~CMASK\)', r'(long)((unsigned long)uclue & ~(unsigned long)CMASK)', content)
    content = re.sub(r'\(long\)\(\(unsigned\s+long\)clues\[j\]\s*&\s*~CMASK\)', r'(long)((unsigned long)clues[j] & ~(unsigned long)CMASK)', content)
    
    # 2. Fix the switch expression
    # switch (op) where op is long. op is already extracted correctly.
    
    # 3. Fix implicit conversions in loops/comparisons
    # j = (int)((op == C_SUB ? (unsigned long)i + value : (unsigned long)i * value));
    # Here value is long.
    content = re.sub(r'\(unsigned\s+long\)i\s*([+*])\s*value', r'(unsigned long)i \1 (unsigned long)value', content)
    
    # total % value
    content = re.sub(r'\(unsigned\s+long\)total\s*%\s*value', r'(unsigned long)total % (unsigned long)value', content)
    
    # (unsigned long)j % value
    content = re.sub(r'\(unsigned\s+long\)j\s*%\s*value', r'(unsigned long)j % (unsigned long)value', content)
    
    # value % (unsigned long)j
    content = re.sub(r'value\s*%\s*\(unsigned\s+long\)j', r'(unsigned long)value % (unsigned long)j', content)

    # 4. Comparisons
    # if (value >= (unsigned long)i)
    content = re.sub(r'if\s*\(value\s*>=\s*\(unsigned\s+long\)i\)', r'if ((unsigned long)value >= (unsigned long)i)', content)
    
    # if ((unsigned long)(j % i) != value)
    content = re.sub(r'if\s*\(\(unsigned\s+long\)\(j\s*%\s*i\)\s*!=\s*value\)', r'if ((unsigned long)(j % i) != (unsigned long)value)', content)
    
    # if ((unsigned long)total == value)
    content = re.sub(r'if\s*\(\(unsigned\s+long\)total\s*==\s*value\)', r'if ((unsigned long)total == (unsigned long)value)', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
