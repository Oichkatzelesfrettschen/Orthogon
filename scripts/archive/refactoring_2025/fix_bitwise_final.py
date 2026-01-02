import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Define constants as (long)UL
    # Replace #define C_EXP 0x80000000UL with #define C_EXP ((long)0x80000000UL)
    content = re.sub(r'#define\s+(C_[A-Z]+)\s+(0x[0-9A-F]+UL)', r'#define \1 ((long)\2)', content)
    content = re.sub(r'#define\s+(CMASK)\s+(0x[0-9A-F]+UL)', r'#define \1 ((long)\2)', content)
    content = re.sub(r'#define\s+(CUNIT)\s+(0x[0-9A-F]+UL)', r'#define \1 ((long)\2)', content)

    # 2. Revert switch expressions to long (or just remove the unsigned cast)
    content = re.sub(r'switch\s*\(\(unsigned\s+long\)\((.*?)\)\s*&\s*CMASK\)', r'switch (\1 & CMASK)', content)
    content = re.sub(r'switch\s*\(\(unsigned\s+long\)\((.*?)\)\)', r'switch (\1)', content)
    
    # 3. Ensure local value/op are long
    content = re.sub(r'unsigned\s+long\s+(value|op)\s*=', r'long \1 =', content)
    
    # 4. Fix value extraction to be signed
    content = re.sub(r'=\s*\(unsigned\s+long\)(.*?)\s*&\s*~CMASK', r'= \1 & ~CMASK', content)

    # 5. Add explicit (long) casts to all clue assignments if missing
    # (Matches any assignment of a constant starting with C_ to a variable or array)
    content = re.sub(r'(\bclue\s*=\s*)(C_[A-Z]+)\b', r'\1(long)\2', content)
    
    # Clean up redundant (long) casts
    content = re.sub(r'\(long\)\(long\)', r'(long)', content)
    content = re.sub(r'\(long\)\(\(long\)', r'((long)', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
