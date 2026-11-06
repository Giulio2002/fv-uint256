#!/usr/bin/env python3
"""g4s2.py: generate lean/Fv256/Amd64/R4ArithS2.lean: B = (Q*M) % 2^320 for the second multiplication (cuts 2f8 .. 47f)."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4arith, g4seg as g
ROOT = '/srv/fv-uint256-wf-r4'
outs = ['x47frbx', 'x47frsi', 'x47fr8', 'x47frax', 'x47fr11']
q = ['x2f8rax', 'x2f8rdx', 'x2f8rcx', 'x2f8r10', 'x2f8r8']; m = ['x2f8m60', 'x2f8m68', 'x2f8m70', 'x2f8rdi']
adc_cuts = [0x3ea, 0x429, 0x46b, 0x47f]; prod_cuts = [0x2f8, 0x33e, 0x38b, 0x3ea]
adc_text, adc_units, adc_in, W = g4arith.unit_chain(adc_cuts, 'adcB', outs)
prod_text, prod_units, prod_in, om = g4arith.prod_units(prod_cuts, 'prodS2', W[0], q, m)
all_cuts = prod_cuts + adc_cuts[1:]
invars, eqs, res = g4arith.chain_data(all_cuts)
# name map adc-local (3ea) -> whole chain actual at 3ea
_, n3ea = g.Ldef(0x3ea)
at3ea = prod_units[-1]['outargs']
amap = dict(zip(n3ea, at3ea))
# map adc actual names (adc chain starts with local 3ea names) -> whole chain names
def amap_name(x): return amap.get(x, x)
# whole-chain final names of outs
_, n47 = g.Ldef(0x47f)
fin = dict(zip(n47, res.values())) if False else res
outs_act = [res[o] for o in outs]
allnew = [n for n, e in eqs]
allv = invars + [n for n in allnew if n not in invars]
out = 'import Fv256.Amd64.R4Seg0\n\nset_option exponentiation.threshold 400\nnamespace Fv256.Amd64.R4Seg\n\n'
out += 'theorem mulb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 := by\n  have := Nat.mul_lt_mul\'\' ha hb\n  rwa [← Nat.pow_add] at this\n\n'
out += prod_text + adc_text
Q = ' + '.join('2 ^ %d * %s' % (64 * i, v) if i else v for i, v in enumerate(q))
M = ' + '.join('2 ^ %d * %s' % (64 * i, v) if i else v for i, v in enumerate(m))
Bs = ' + '.join('2 ^ %d * %s' % (64 * i, v) if i else v for i, v in enumerate(outs_act))
full = ' + '.join('2 ^ %d * (%s * %s)' % (64 * (i + j), m[j], q[i]) for i in range(5) for j in range(4))
out += 'theorem s2_arith (%s : Nat)\n' % ' '.join(allv)
for v in invars: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
for n, e in eqs: out += '    (h_%s : %s = %s)\n' % (n, n, e)
out += '    : %s = ((%s) * (%s)) %% 2 ^ 320 := by\n' % (Bs, Q, M)
# bounds for all new vars
for n, e in eqs:
    out += '  have b_%s : %s < 2 ^ 64 := by\n    first | (rw [h_%s]; exact Nat.mod_lt _ (by decide)) | (rw [h_%s]; exact BitVec.isLt _)\n' % (n, n, n, n)
def call(lname, allv_u, in_act, eqs_u, mp, tag):
    args = ' '.join(mp(v) for v in allv_u)
    bs = ' '.join('b_%s' % mp(v) for v in in_act)
    hs = ' '.join('h_%s' % mp(n) for n, e in eqs_u)
    return '  have %s := %s %s %s %s\n' % (tag, lname, args, bs, hs)
tags = []
for k, u in enumerate(prod_units):
    out += call(u['lname'], u['allv'], u['in_act'], u['eqs'], lambda x: x, 'p%d' % k); tags.append('p%d' % k)
for k, u in enumerate(adc_units):
    out += call(u['lname'], u['allv'], u['in_act'], u['eqs'], amap_name, 'a%d' % k); tags.append('a%d' % k)
root = {}
for n, e in eqs:
    mm = re.fullmatch(r'(x[0-9a-f]+[a-z0-9]+) % 18446744073709551616', e.strip())
    if mm:
        r = root.get(mm.group(1), mm.group(1))
        root[n] = r
        out += '  have e_%s : %s = %s := by rw [h_%s]; exact (Nat.mod_eq_of_lt b_%s).symm\n  subst e_%s\n' % (n, r, n, n, r, n)
out += '  have hfull : (%s) * (%s) = %s := by janus_ring\n' % (Q, M, full)
for i in range(5):
    for j in range(4): out += '  have mb%d%d := mulb %s %s b_%s b_%s\n' % (i, j, m[j], q[i], m[j], q[i])
out += '  clear %s\n' % ' '.join('h_' + n for n, e in eqs)
chain = tags[-1]
for t_ in reversed(tags[:-1]): chain = '%s.trans (%s)' % (t_, chain)
out += '  have hchain := %s\n' % chain
out += '  clear %s\n' % ' '.join(tags)
out += '  have hBlt : %s < 2 ^ 320 := by omega\n' % Bs
out += '  rw [hfull]\n  omega\n\nend Fv256.Amd64.R4Seg\n'
open(ROOT + '/lean/Fv256/Amd64/R4ArithS2.lean', 'w').write(out)
print(len(out), len(allv), len(eqs))
