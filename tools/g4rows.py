#!/usr/bin/env python3
"""g4rows.py: row-level invariant lemmas with a capacity hypothesis."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4chain, g4seg as g, g4w2, g4eq, g4anf
def rows(cuts, finalw, name, dropped=None):
    om = g4w2.weights_chain(cuts, finalw)
    units = [g4chain.load(a, b) for a, b in zip(cuts, cuts[1:])]
    inact = [units[0]['invars']]
    for k in range(1, len(units)):
        u = units[k]; actual = units[k - 1]['outargs']
        mp = dict(zip(u['invars'], actual))
        sub = lambda s, mp=mp: re.sub(r'\bx[0-9a-f]+[a-z0-9]+\b', lambda m: mp.get(m.group(0), m.group(0)), s)
        u['eqs'] = [(n, sub(e)) for n, e in u['eqs']]
        u['outargs'] = [mp.get(a, a) for a in u['outargs']]
        inact.append(actual)
    names = [g.Ldef(c)[1] for c in cuts]
    def term(v, w):
        e = w.bit_length() - 1
        return v if e == 0 else '%d * %s' % (1 << e, v)
    text = ''; info = []
    for k, u in enumerate(units):
        a, b = cuts[k], cuts[k + 1]
        eq0 = g4eq.eqs(a, b); txt = ' '.join(e for n, e in eq0)
        nA = names[k]; nB = names[k + 1]
        in_act = inact[k]; out_act = u['outargs']
        cons = [i for i in range(len(nA)) if re.search(r'\b%s\b' % nA[i], txt) and nA[i] in om[k]]
        newo = [n for n, e in eq0 if n in om[k + 1]]
        cap_e = max(om[k + 1][n] for n in newo).bit_length() - 1 + 64 if newo else None
        lhs = ' + '.join(term(in_act[i], om[k][nA[i]]) for i in range(len(nA)) if nA[i] in om[k]) or '0'
        rhs = ' + '.join(term(out_act[i], om[k + 1][nB[i]]) for i in range(len(nB)) if nB[i] in om[k + 1]) or '0'
        S = ' + '.join(term(in_act[i], om[k][nA[i]]) for i in cons) or '0'
        newv = [n for n, e in u['eqs']]
        allv = list(dict.fromkeys(in_act + newv + out_act))
        th = 'theorem %s_r%d ' % (name, k) + '(%s : Nat)\n' % ' '.join(allv)
        for v in in_act: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
        for n, e in u['eqs']: th += '    (h_%s : %s = %s)\n' % (n, n, e)
        th += '    (hcap : %s < %d)\n' % (S, 1 << cap_e)
        extra = ''
        if dropped and k in dropped: extra = ' + ' + dropped[k](in_act, nA)
        th += '    : %s = %s%s := by\n' % (lhs, rhs, extra)
        th += '\n'.join(g4anf.anf([e for n, e in u['eqs']], 'r%d' % k)) + '\n  omega\n\n'
        text += th
        info.append(dict(k=k, S=S, cap=cap_e, lhs=lhs, rhs=rhs, in_act=in_act, out_act=out_act, allv=allv, eqs=u['eqs'], cons=[in_act[i] for i in cons]))
    return text, info, om, units
if __name__ == '__main__':
    cuts = [0x1cd, 0x1d9, 0x1f2, 0x20c, 0x236, 0x25b, 0x290, 0x2b5, 0x2e0, 0x2f8]
    qn = ['x2f8rax', 'x2f8rdx', 'x2f8rcx', 'x2f8r10', 'x2f8r8']
    fw = {n: 1 << (320 + 64 * i) for i, n in enumerate(qn)}
    dropped = {7: lambda ia, nA: '2 ^ 256 * ((%s + %s) %% 2 ^ 64)' % (ia[nA.index('x2b5r11')], ia[nA.index('x2b5ma8')])}
    t, info, om, units = rows(cuts, fw, 's1', dropped)
    open('/srv/fv-uint256-wf-r4/lean/Fv256/Amd64/R4ArithRows.lean', 'w').write("import Fv256.Amd64.R4Seg0\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n" + t + "\nend Fv256.Amd64.R4Seg\n")
    for i in info: print(i['k'], i['cap'], i['S'][:80])
