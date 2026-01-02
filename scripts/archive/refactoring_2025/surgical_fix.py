import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Fix the broken lines like: unsigned long value = (long)((unsigned long)ctx->clues[box] & ~CMASK));
    # to: unsigned long value = (unsigned long)ctx->clues[box] & ~CMASK;
    # CMASK is UL so ~CMASK is UL.
    
    # Pattern for broken line
    pattern = r'unsigned\s+long\s+(\w+)\s*=\s*\(long\)\(\(unsigned\s+long\)(.*?)\s*&\s*~CMASK\)\);'
    replacement = r'unsigned long \1 = (unsigned long)\2 & ~CMASK;'
    content = re.sub(pattern, replacement, content)
    
    # Also fix any sprintf if broken
    content = re.sub(r'p\s*\+=\s*sprintf\(p,\s*"%05lu",\s*\(long\)\(\(unsigned\s+long\)(.*?)\s*&\s*~CMASK\)\);',
                     r'p += sprintf(p, "%05lu", (unsigned long)\1 & ~CMASK);', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
