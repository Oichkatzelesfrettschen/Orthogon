import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Fix assignments: clue = C_... -> clue = (long)C_...
    # Matches clue = C_EXP or clues[j] = C_ADD etc.
    content = re.sub(r'(\bclue\s*=\s*)(C_[A-Z]+)\b', r'\1(long)\2', content)
    content = re.sub(r'(\bclues\[[a-z]+\]\s*=\s*)(C_[A-Z]+)\b', r'\1(long)\2', content)
    
    # Fix switch cases if needed?
    # Actually, the error suggested case labels were problematic.
    # But let's try the assignments first.
    
    with open(path, 'w') as f:
        f.write(content)

fix_file('app/src/main/jni/keen.c')
