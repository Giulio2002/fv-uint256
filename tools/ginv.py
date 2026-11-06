#!/usr/bin/env python3
"""ginv.py: invariant-chain proofs for add/adc accumulation chains.
usage (python): import ginv; ginv.build(cuts, target, name) ; see bottom.
For consecutive cuts it finds, by exact linear algebra over random samples, weights alpha^c_v (v in live vars of L_c) with
  sum alpha^c_v * v == TARGET(start vars)   at every cut c,
then emits one janus_carry lemma per segment:  INV_out = INV_in   (hypotheses: bounds of in-vars, defining equations of new vars)."""
import sys, os, re, random, ast
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
import gchain, gnum
M = 2 ** 64
def solve(rows, rhs):
    n = len(rows[0]); m = len(rows)
    A = [[Fraction(x) for x in r] + [Fraction(b)] for r, b in zip(rows, rhs)]
    piv = []; r = 0
    for c in range(n):
        p = None
        for i in range(r, m):
            if A[i][c] != 0: p = i; break
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        inv = 1 / A[r][c]
        A[r] = [x * inv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    for i in range(r, m):
        if A[i][n] != 0: return None
    sol = [Fraction(0)] * n
    for i, c in enumerate(piv): sol[c] = A[i][n]
    return sol
def sample_chain(units, nsamp, gen=None):
    out = []
    for _ in range(nsamp):
        env = {v: random.randrange(M) for v in units[0]['invars']}
        if gen: gen(env)
        snaps = [dict(env)]
        for u in units:
            for n, e in u['eqs']:
                env[n] = eval(gnum.conv(e), {'D': gnum.D}, env)
            snaps.append(dict(env))
        out.append(snaps)
    return out
def weights(units, target, nsamp=None, gen=None):
    """target: function env0 -> int (env0 = dict of start vars). returns list (per cut) of dict var->int weight"""
    names = [units[0]['invars']] + [u['outargs'] for u in units]
    n = max(len(x) for x in names)
    nsamp = nsamp or n + 8
    samples = sample_chain(units, nsamp, gen)
    res = []
    for k, nm in enumerate(names):
        rows = [[s[k][v] for v in nm] for s in samples]
        rhs = [target(s[0]) for s in samples]
        sol = solve(rows, rhs)
        if sol is None: raise Exception('no weights at cut %d' % k)
        w = {}
        for v, a in zip(nm, sol):
            if a != 0:
                assert a.denominator == 1, ('non-integer weight', v, a)
                w[v] = int(a)
        res.append(w)
    return res
def wtxt(w):
    def one(v, a):
        for k in range(0, 12):
            if a == M ** k: return v if k == 0 else '2 ^ %d * %s' % (64 * k, v)
        return '%d * %s' % (a, v)
    return ' + '.join(one(v, a) for v, a in w.items()) or '0'

def emit_lemmas(prefix, cuts, W, units, last_carry=None, tight=()):
    """lemma inv_<prefix>_<k> for each unit k; returns lean text and list of lemma names/args"""
    out = []; info = []
    for k, u in enumerate(units):
        inv = u['invars']; outs = u['outargs']; eqs = u['eqs']
        newv = [n for n, e in eqs]
        allv = list(dict.fromkeys(inv + newv))
        bounds = ' '.join('(hb_%s : %s < %s)' % (v, v, '18446744073709551615' if v in tight else '2 ^ 64') for v in inv)
        hyps = ' '.join('(h_%s : %s = %s)' % (n, n, e) for n, e in eqs)
        name = 'inv_%s_%d' % (prefix, k)
        lhs = wtxt(W[k + 1]); rhs = wtxt(W[k])
        extra = ''
        goal = '%s = %s' % (lhs, rhs)
        if last_carry and k == len(units) - 1:
            goal = '%s + 2 ^ 448 * (%s) = %s' % (lhs, last_carry(units), rhs)
        txt = 'theorem %s (%s : Nat) %s\n    %s : %s := by\n  subst %s\n  janus_carry\n' % (
            name, ' '.join(allv), bounds, hyps, goal, ' '.join('h_' + n for n in newv))
        out.append(txt); info.append((name, allv, inv, newv))
    return '\n'.join(out), info
