import re

def fix_bitwise(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Define constants as UL
    content = re.sub(r'#define\s+(C_[A-Z]+)\s+0x[0-9A-F]+L', lambda m: m.group(0).replace('L', 'UL'), content)
    content = re.sub(r'#define\s+CMASK\s+0x[0-9A-F]+L', lambda m: m.group(0).replace('L', 'UL'), content)
    
    # 2. Fix assignments: clue = C_... -> clue = (long)C_...
    content = re.sub(r'(\bclue\s*=\s*)(C_[A-Z]+)\b', r'\1(long)\2', content)
    content = re.sub(r'(\bclues\[[a-z]+\]\s*=\s*)(C_[A-Z]+)\b', r'\1(long)\2', content)
    
    # 3. Fix switch expressions: switch (clue & CMASK) -> switch ((unsigned long)clue & CMASK)
    # This handles both local 'clue' and 'clues[j]'
    content = re.sub(r'switch\s*\(([^)]*?clue[^)]*?)\s*&\s*CMASK\)', r'switch ((unsigned long)(\1) & CMASK)', content)
    
    # 4. Fix value extraction: long target = clue & ~CMASK -> long target = (long)((unsigned long)clue & ~CMASK)
    content = re.sub(r'(\blong\s+\w+\s*=\s*)([^;]*?clue[^;]*?\s*&\s*~CMASK)', r'\1(long)((unsigned long)(\2))', content)
    # Simplify if it's already got some parts
    content = re.sub(r'\(long\)\(\(unsigned long\)\(\(unsigned long\)', r'(long)((unsigned long)', content)

    with open(path, 'w') as f:
        f.write(content)

fix_bitwise('app/src/main/jni/keen.c')
fix_bitwise('app/src/main/jni/keen_validate.c')
