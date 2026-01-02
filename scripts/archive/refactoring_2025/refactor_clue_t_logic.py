import re

def fix_file(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Use clue_t everywhere for clues pointers
    content = re.sub(r'\blong\s*\*\s*clues\b', 'clue_t* clues', content)
    
    # JNI: casting jlong to clue_t
    content = re.sub(r'clues\[i\]\s*=\s*\(long\)clues_body\[i\];', 'clues[i] = (clue_t)clues_body[i];', content)
    content = re.sub(r'clues\[i\]\s*=\s*clues_body\[i\];', 'clues[i] = (clue_t)clues_body[i];', content)
    content = re.sub(r'\bsnewn\s*\((.*?),\s*long\)', r'snewn(\1, clue_t)', content)

    # Arithmetic Extraction: remove complex casts, use clue_t directly
    # Example: long value = (long)((unsigned long)uclue & ~CMASK);
    # To: clue_t value = uclue & ~CMASK;
    # But KenKen arithmetic needs the value part.
    # Standard: uint64_t val = uclue & ~CMASK;
    content = re.sub(r'long\s+(value|op|target)\s*=\s*\(long\)\(\(unsigned\s+long\)uclue\s*&\s*~CMASK\);', r'clue_t \1 = uclue & ~CMASK;', content)
    content = re.sub(r'long\s+(value|op|target)\s*=\s*\(long\)\(\(unsigned\s+long\)uclue\s*&\s*CMASK\);', r'clue_t \1 = uclue & CMASK;', content)
    
    # Generic extraction from clues array
    content = re.sub(r'long\s+target\s*=\s*\(long\)\(\(unsigned\s+long\)(.*?clues\[.*?\])\s*&\s*~CMASK\);', r'clue_t target = (clue_t)(\1) & ~CMASK;', content)
    content = re.sub(r'long\s+op\s*=\s*\(long\)\(\(unsigned\s+long\)(.*?clues\[.*?\])\s*&\s*CMASK\);', r'clue_t op = (clue_t)(\1) & CMASK;', content)

    # sprintf %ld -> %llu or %PRIu64
    content = re.sub(r'"%05ld"', r'"%05" PRIu64', content)
    # Actually, %05lu is fine for uint64_t if we use the correct PRI macro,
    # but for simplicity in this turn, I'll use %05llu which is widely supported.
    content = re.sub(r'"%05ld"', r'"%05llu"', content)
    content = re.sub(r'\(long\)\(\(unsigned\s+long\)clues\[j\]\s*&\s*~CMASK\)', r'(unsigned long long)(clues[j] & ~CMASK)', content)

    with open(path, 'w') as f:
        f.write(content)

for p in ['app/src/main/jni/keen.c', 'app/src/main/jni/keen-android-jni.c', 'app/src/main/jni/keen_validate.c', 'app/src/main/jni/keen_hints.c']:
    fix_file(p)
