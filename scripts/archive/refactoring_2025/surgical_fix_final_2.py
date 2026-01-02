import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Constants: No (long) cast, just UL
    content = re.sub(r'#define\s+(C_[A-Z]+)\s+\(\(long\)(0x[0-9A-F]+UL)\)', r'#define \1 \2', content)
    content = re.sub(r'#define\s+(CMASK)\s+\(\(long\)(0x[0-9A-F]+UL)\)', r'#define \1 \2', content)
    content = re.sub(r'#define\s+(CUNIT)\s+\(\(long\)(0x[0-9A-F]+UL)\)', r'#define \1 \2', content)

    # 2. Extract op and value as unsigned long
    # Example: long value = (long)((unsigned long)uclue & ~CMASK);
    content = re.sub(r'long\s+value\s*=\s*\(long\)\((.*?uclue.*?)\s*&\s*~CMASK\);', r'unsigned long value = \1 & ~CMASK;', content)
    content = re.sub(r'long\s+op\s*=\s*\(long\)\((.*?uclue.*?)\s*&\s*CMASK\);', r'unsigned long op = \1 & CMASK;', content)
    
    # 3. Switch statements: ensure unsigned long expression
    # switch (op) -> switch ((unsigned long)op)
    content = re.sub(r'switch\s*\(\s*op\s*\)', r'switch ((unsigned long)op)', content)
    # switch ((unsigned long)clues[j] & CMASK) -> already correct
    
    # 4. Comparisons: ensure both sides unsigned
    # if (sum == (long)target) -> if ((unsigned long)sum == target)
    content = re.sub(r'(\w+)\s*==\s*\(long\)target', r'(unsigned long)\1 == target', content)
    content = re.sub(r'(\w+)\s*==\s*\(long\)value', r'(unsigned long)\1 == value', content)
    
    # labs conversion
    content = re.sub(r'\(long\)target\s*==\s*\(long\)labs', r'target == (unsigned long)labs', content)
    content = re.sub(r'a\s*/\s*b\s*==\s*\(long\)target', r'(unsigned long)(a / b) == target', content)
    
    # pow
    content = re.sub(r'pow_ab\s*<=\s*\(long\)target', r'pow_ab <= (long)target', content)
    content = re.sub(r'pow_ba\s*<=\s*\(long\)target', r'pow_ba <= (long)target', content)
    content = re.sub(r'==\s*\(long\)target', r'== (long)target', content)

    # 5. sprintf
    content = re.sub(r'p\s*\+=\s*sprintf\(p,\s*"%05ld",\s*\(long\)\(\(unsigned\s+long\)(.*?)\s*&\s*~CMASK\)\);',
                     r'p += sprintf(p, "%05lu", (unsigned long)\1 & ~CMASK);', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
