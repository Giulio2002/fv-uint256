#!/usr/bin/env python3
"""geq.py A B [var...]: print equations (name = expr) of segment P_A_B as Lean hypotheses `(h_name : name = expr)`"""
import re, sys
def eqs(A, B):
    t = open('/srv/fv-uint256-wf-r4/lean/Fv256/Proofs/Amd64/R4G/G_%x_%x.lean' % (A, B)).read()
    i = t.index('def P_'); j = t.index('\n\nset_option', i)
    d = t[i:j]
    pat = re.compile(r' ∧ (x[0-9a-f]+[a-z0-9]+) = | ∧ R4Regs')
    ms = list(pat.finditer(d))
    out = []
    for a, m in enumerate(ms):
        if m.group(1) is None: break
        end = ms[a + 1].start() if a + 1 < len(ms) else len(d)
        out.append((m.group(1), d[m.end():end].strip()))
    return out
if __name__ == '__main__':
    A, B = int(sys.argv[1], 16), int(sys.argv[2], 16)
    want = sys.argv[3:]
    for n, e in eqs(A, B):
        if not want or n in want: print('(h_%s : %s = %s)' % (n, n, e))
