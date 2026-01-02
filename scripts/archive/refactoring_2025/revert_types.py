import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Revert unsigned long* clues back to long* clues
    content = re.sub(r'\bunsigned long\s*\*\s*clues\b', 'long* clues', content)
    content = re.sub(r'\bunsigned long\s*\*\s*cluevals\b', 'long* cluevals', content)
    
    # Revert struct clues
    content = re.sub(r'unsigned long\* clues;', 'long* clues;', content)
    
    # Revert allocations
    content = re.sub(r'(\bclues\s*=\s*snewn\s*\([^,]+,\s*)unsigned long\b', r'\1long', content)
    content = re.sub(r'(\bcluevals\s*=\s*snewn\s*\([^,]+,\s*)unsigned long\b', r'\1long', content)
    
    # Revert solver signature
    content = re.sub(r'static int solver\(int w, int\* dsf, unsigned long\* clues', 'static int solver(int w, int* dsf, long* clues', content)

    with open(path, 'w') as f:
        f.write(content)

for p in ['app/src/main/jni/keen.c', 'app/src/main/jni/keen-android-jni.c', 'app/src/main/jni/keen_validate.c', 'app/src/main/jni/keen_hints.c', 'app/src/main/jni/keen_validate.h', 'app/src/main/jni/keen_hints.h']:
    fix_file(p)
