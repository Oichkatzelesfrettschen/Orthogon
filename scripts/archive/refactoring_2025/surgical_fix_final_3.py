import re

def fix_validate(path):
    with open(path, 'r') as f:
        content = f.read()
    
    # Change intermediate calculation types to unsigned long
    content = re.sub(r'long\s+(sum|prod|pow_ab|pow_ba|g|l|x)\s*=', r'unsigned long \1 =', content)
    
    # Remove redundant (long) casts in comparisons against target
    content = re.sub(r'==\s*\(long\)target', r'== target', content)
    content = re.sub(r'==\s*\(long\)labs', r'== target', content) # special case
    
    # Fix labs and target comparison
    # return (long)target == (long)labs(values[0] - values[1]);
    content = re.sub(r'return\s+\(long\)target\s*==\s*\(long\)labs\(values\[0\]\s*-\s*values\[1\]\);',
                     r'return target == (unsigned long)labs(values[0] - values[1]);', content)

    # Fix pow loop comparison
    content = re.sub(r'pow_ab\s*<=\s*\(long\)target', r'pow_ab <= target', content)
    content = re.sub(r'pow_ba\s*<=\s*\(long\)target', r'pow_ba <= target', content)

    # Fix division
    content = re.sub(r'a\s*/\s*b\s*==\s*\(long\)target', r'(unsigned long)(a / b) == target', content)
    
    with open(path, 'w') as f:
        f.write(content)

fix_validate('app/src/main/jni/keen_validate.c')
