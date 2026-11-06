#!/usr/bin/env python3
"""g4w2.py: weights with a dropped column: backward finite differences; zero-effect variables that occur in the chain's equations get weight 2^dropexp."""
import sys, random, os, re
sys.path.insert(0, os.path.dirname(__file__))
import g4sim, g4seg as g, g4eq
M64 = 1 << 64
def weights_chain(cuts, finalw, dropexp=256, trials=3):
    """finalw: {name at last cut: integer weight}. returns list om[k] (dict name->integer weight, 0 omitted)"""
    nu = len(cuts) - 1
    names = [g.Ldef(c)[1] for c in cuts]
    used = [set() for _ in cuts]       # names (local) read by the unit's equations
    for k in range(nu):
        itsA = g.items(cuts[k]); nA = names[k]
        txt = ' '.join(e for n, e in g4eq.eqs(cuts[k], cuts[k + 1]))
        used[k] = {n for n in nA if re.search(r'\b%s\b' % n, txt)}
    om = [None] * (nu + 1); om[nu] = dict(finalw)
    for k in range(nu - 1, -1, -1):
        a, b = cuts[k], cuts[k + 1]; nA = names[k]
        def psiB(env): return sum(om[k + 1].get(n, 0) * v for n, v in env.items())
        w = {}
        for n in nA:
            ds = set()
            for t in range(trials):
                base = {x: random.randrange(M64) for x in nA}
                b0 = psiB(g4sim.step(base, a, b)); e = dict(base); e[n] += 1
                ds.add(psiB(g4sim.step(e, a, b)) - b0)
            if len(ds) == 1:
                d = ds.pop()
            else:
                raise Exception('inconsistent %s %s' % (n, ds))
            if d == 0 and n in used[k]: d = 1 << dropexp
            if d: w[n] = d
        om[k] = w
    return om
