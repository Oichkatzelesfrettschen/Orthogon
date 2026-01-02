import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Replace long* clues with unsigned long* clues in variable declarations
    content = re.sub(r'\blong\s*\*\s*clues\b', 'unsigned long* clues', content)
    
    # Fix assignments: long clue = ctx->clues[root] -> unsigned long clue = ...
    content = re.sub(r'\blong\s+clue\s*=\s*ctx->clues', 'unsigned long clue = ctx->clues', content)
    
    # Fix allocations: clues = snewn(..., long) -> snewn(..., unsigned long)
    content = re.sub(r'(\bclues\s*=\s*snewn\s*\([^,]+,\s*)long\b', r'\1unsigned long', content)
    
    with open(path, 'w') as f:
        f.write(content)

for p in ['app/src/main/jni/keen-android-jni.c', 'app/src/main/jni/keen_validate.c', 'app/src/main/jni/keen_hints.c']:
    fix_file(p)
