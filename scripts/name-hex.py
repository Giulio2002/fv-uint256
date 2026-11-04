#!/usr/bin/env python3
"""Replace address literals in the STATEMENTS (correctness, pre, nonvacuous) of the hex proofs by the extraction's named
data constants (errBase / tabBase from SetFromHexLoops); each proof starts by rewriting them back with errBase_val/tabBase_val."""
import re, sys
isa = sys.argv[1]
EB, TB = (1792784, 1002789) if isa == 'Arm64' else (5995344, 5176782)
def sub(seg):
    for n, name in ((EB + 96, '(errBase + 96)'), (EB, 'errBase'), (TB + 256, '(tabBase + 256)'), (TB, 'tabBase')):
        seg = re.sub(r'(?<![\w.#])%d(?![\w])' % n, name, seg)
    return seg
for p in sys.argv[2:]:
    s = open(p).read()
    out, i = '', 0
    for m in re.finditer(r'theorem (correctness|pre|nonvacuous)\b', s):
        if m.start() < i: continue
        j = s.index(':=', m.start())
        # statement ends at the first `:=` at depth 0 after the signature; theorem statements here contain no `:=` before it
        out += s[i:m.start()] + sub(s[m.start():j]); i = j
    out += s[i:]
    # proof start: after `intro ret hret s hs ...` line of correctness
    out = re.sub(r'(\n  intro ret hret s hs[^\n]*\n)', r'\1  simp only [errBase_val, tabBase_val] at *\n', out, count=1)
    open(p, 'w').write(out); print('named', p)
