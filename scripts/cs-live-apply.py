#!/usr/bin/env python3
"""cs-live-apply.py FILE CFGNAME THEOREM [THEOREM...] : insert the Live call-site block (cs_live_gen) into FILE.
Block goes before the doc comment of the FIRST listed theorem; statement conjuncts before `RetAddr` inside each listed
theorem statement; proof terms are inserted before the first `hret` that follows `:=` of each listed theorem (anonymous-constructor
proofs) -- wrappers that use `obtain/exact` are handled by --wrap."""
import sys, re
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cs_live_gen import block
CFG = {
 'afd': dict(B='0x400', R2='(R3 TW)', nok=6, pos=dict(new=0, w1=2, w2=3, mg=4, mv=5), newty='numErrT', dst='zW', src='0x301000'),
 'ut': dict(B='bW', R2='R0', nok=6, pos=dict(new=0, w1=1, w2=2, mg=3, mv=4, sb=5), newty='numErrT', dst='zW', src='0x301000', sb=True,
            sb_addr='Fv256.Amd64.UnmarshalTextS.sbAddr', st_addr='Fv256.Amd64.UnmarshalTextS.stAddr', sb_buf='0', sb_p='0x301000',
            sb_ok='⟨rfl, 0, 0x301000, by decide, Or.inl (by decide)⟩'),
 'sfd': dict(B='0x400', R2='R0', nok=5, pos=dict(new=0, w1=1, w2=2, mg=3, mv=4), newty='numErrT', dst='zW', src='0x301000'),
}
def main():
    f, name = sys.argv[1], sys.argv[2]
    rest = sys.argv[3:]
    core = []; wrap = []; cur = core
    for x in rest:
        if x == '--core': cur = core
        elif x == '--wrap': cur = wrap
        else: cur.append(x)
    s = open(f).read()
    defs, stmt, terms = block(CFG[name])
    first = s.index('\n')
    if 'CallSites.Live' not in s:
        s = s[:first] + '\nimport Fv256.Amd64.CallSites.Live' + s[first:]
    if core:
        i = s.index('theorem ' + core[0] + ' ')
        pre = s[:i].rstrip('\n')
        j = pre.rindex('/--') if pre.endswith('-/') else i
        lines = s[:j].rstrip('\n').split('\n')
        if lines and lines[-1].startswith('set_option') and lines[-1].rstrip().endswith(' in'):
            j = len('\n'.join(lines[:-1])) + 1
        s = s[:j] + 'open Fv256.CallSites\n\n' + defs + '\n' + s[j:]
    for t in core + wrap:
        i = s.index('theorem ' + t + ' ')
        r = s.index('    RetAddr (Extracted.program.link impl) ret ∧', i)
        s = s[:r] + stmt + s[r:]
        h = s.index(':=', r)
        if t in core:
            m = s.index('hret', h)
            s = s[:m] + ', '.join(terms) + ', ' + s[m:]
        else:
            names = ', '.join('cs%d' % (k + 1) for k in range(len(terms)))
            m1 = s.index('hret, hsetup', h)
            s = s[:m1] + names + ', ' + s[m1:]
            m2 = s.index('hret, hsetup', m1 + len(names) + 2)
            s = s[:m2] + names + ', ' + s[m2:]
    open(f, 'w').write(s)
main()
