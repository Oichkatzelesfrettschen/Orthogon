import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Constants: ensure they are UL, no (long) cast
    content = re.sub(r'#define\s+(C_[A-Z]+)\s+\(\(long\)(0x[0-9A-F]+UL)\)', r'#define \1 \2', content)
    content = re.sub(r'#define\s+(CMASK)\s+\(\(long\)(0x[0-9A-F]+UL)\)', r'#define \1 \2', content)
    
    # 2. Variable types: op and value should be unsigned long
    content = re.sub(r'\blong\s+(target|op|value)\s*=', r'unsigned long \1 =', content)
    
    # 3. Extraction logic
    content = re.sub(r'unsigned\s+long\s+target\s*=\s*\(long\)\(\(unsigned\s+long\)uclue\s*&\s*~CMASK\);',
                     r'unsigned long target = uclue & ~CMASK;', content)
    content = re.sub(r'unsigned\s+long\s+op\s*=\s*\(long\)\(\(unsigned\s+long\)uclue\s*&\s*CMASK\);',
                     r'unsigned long op = uclue & CMASK;', content)
    
    # 4. Comparisons: sum == (long)target -> sum == (long)target (wait, if target is unsigned, this is fine)
    # Actually, let's cast target to long for comparisons if sum is long.
    content = re.sub(r'sum\s*==\s*target', r'sum == (long)target', content)
    content = re.sub(r'prod\s*==\s*target', r'prod == (long)target', content)
    content = re.sub(r'g\s*==\s*target', r'g == (long)target', content)
    content = re.sub(r'l\s*==\s*target', r'l == (long)target', content)
    content = re.sub(r'x\s*==\s*target', r'x == (long)target', content)
    content = re.sub(r'pow_ab\s*==\s*target', r'pow_ab == (long)target', content)
    content = re.sub(r'pow_ba\s*==\s*target', r'pow_ba == (long)target', content)
    content = re.sub(r'pow_ab\s*<=\s*target', r'pow_ab <= (long)target', content)
    content = re.sub(r'pow_ba\s*<=\s*target', r'pow_ba <= (long)target', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
