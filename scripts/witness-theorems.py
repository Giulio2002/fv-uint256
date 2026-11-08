#!/usr/bin/env python3
"""scripts/witness-theorems.py FILE  : print the fully qualified name of every witness theorem declared in FILE.
A witness theorem is a theorem declared inside a namespace whose name contains `Witness` (e.g. Fv256.Amd64.Add.Witness.nonvacuous,
...Grow.Witness.nonvacuous, ...Witness.big) whose statement is an existential (`: ∃ ...`).  Helper theorems in the Witness namespace
(setup, hpre, hret, ...) are not existentials and are skipped."""
import re, sys
src = open(sys.argv[1], errors='ignore').read()
# strip comments (-- line and /- -/ block, non-nested enough for these files)
src = re.sub(r'/-.*?-/', '', src, flags=re.S)
src = re.sub(r'--[^\n]*', '', src)
ns = []
out = []
pos = 0
tok = re.compile(r'^[ \t]*(namespace\s+(\S+)|end\s+(\S+)|(?:private\s+)?theorem\s+(\S+))', re.M)
ms = list(tok.finditer(src))
for k, m in enumerate(ms):
    if m.group(2): ns.append(m.group(2)); continue
    if m.group(3):
        if ns and ns[-1] == m.group(3): ns.pop()
        continue
    name = m.group(4)
    if not any('Witness' in n for n in ns): continue
    end = ms[k + 1].start() if k + 1 < len(ms) else len(src)
    body = src[m.end():end]
    j = body.find(':=')
    hdr = body[:j] if j >= 0 else body
    depth = 0; flat = []
    for ch in hdr:
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif depth == 0: flat.append(ch)
    flat = ''.join(flat)
    # UP3d (03aa338e): strict by-name pairing: `Witness.nonvacuous` pairs with `correctness`; any other `Witness.<X>` needs a main named `<X>`, so only the nonvacuous witnesses are passed to janus verify
    # (the other witness theorems stay in the module and are kernel-checked with it, but are not audited as witnesses)
    if name == 'nonvacuous' and re.match(r'\s*:\s*∃', flat):
        out.append('.'.join(ns + [name]) if not name.startswith('_root_') else name)
print('\n'.join(out))
