import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # 1. Fix reading from clues array into unsigned long clue
    # Example: unsigned long clue = ctx->clues[root];
    content = re.sub(r'unsigned\s+long\s+clue\s*=\s*(.*?clues\[.*?\])', r'unsigned long clue = (unsigned long)(\1)', content)
    
    # 2. Fix assignments back to clues array
    # Example: clues[new_canon] = C_ADD | new_val;
    # where C_ADD is UL.
    content = re.sub(r'(clues\[.*?\]\s*=\s*)(C_[A-Z]+\s*\|\s*new_val)', r'\1(long)(\2)', content)

    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
fix_file('app/src/main/jni/keen_validate.c')
fix_file('app/src/main/jni/keen_hints.c')
