#!/usr/bin/env python3
"""g4sim.py: numeric simulation of generated segment units (to find / check arithmetic invariants)."""
import re, random, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import g4eq, g4seg as g
M64 = 1 << 64
def pyexpr(e):
    e = re.sub(r'\(BitVec\.ofNat 64 (\w+) - BitVec\.ofNat 64 (\w+)\)\.toNat', r'((\1 - \2) % 18446744073709551616)', e)
    e = e.replace(' / ', ' // ')
    e = re.sub(r'if (.*?) then (.*?) else (.*)$', lambda m: '(%s) if (%s) else (%s)' % (m.group(2), m.group(1), m.group(3)), e)
    return e
def step(env, A, B):
    """apply unit A->B: returns env with names of cut B filled (unchanged vars renamed)"""
    itsA = g.items(A); itsB = g.items(B)
    _, nA = g.Ldef(A); _, nB = g.Ldef(B)
    mapA = {it: n for it, n in zip(itsA, nA)}
    eqs = dict(g4eq.eqs(A, B))
    out = dict(env)
    for it, n in zip(itsB, nB):
        if n in eqs:
            out[n] = eval(pyexpr(eqs[n]), {}, dict(out))
        else:
            out[n] = out[mapA[it]]
    return out
def run(A_cuts, env0):
    env = dict(env0)
    for a, b in zip(A_cuts, A_cuts[1:]): env = step(env, a, b)
    return env
