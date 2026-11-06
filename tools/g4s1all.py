#!/usr/bin/env python3
"""g4s1all.py: whole S1 (cut 0x1cd -> 0x2f8) as a single lemma over the product atoms, proved by ANF + omega."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4arith, g4seg as g, g4hi, g4w2, g4anf
ROOT = '/srv/fv-uint256-wf-r4'
cuts = [0x1cd, 0x25b, 0x2b5, 0x2f8]
qn = ['x2f8rax', 'x2f8rdx', 'x2f8rcx', 'x2f8r10', 'x2f8r8']
finalw = {n: 1 << (320 + 64 * i) for i, n in enumerate(qn)}
om = g4w2.weights_chain(cuts, finalw)
invars, eqs, res = g4arith.chain_data(cuts)       # x1cd* in, chain eqs
hi = g4hi.hi_names()
def conv(e):
    def rl(mo):
        base = mo.group(1); off = int(mo.group(2) or 0)
        return {'3': 'X', '7': 'U', '1': 'M'}[base] + str(off // 8)
    e = re.sub(r'Arm64\.Memory\.readLE s\.mem \(BitVec\.toNat \(s\.regs (\d)\)(?: \+ (\d+))?\) 8', rl, e)
    return e
word_eqs = []
for n, (v, e) in hi.items():
    if 'regs 0' in e: continue
    word_eqs.append((n, '(%s) %% 18446744073709551616' % conv(e)))
atoms = set()
for n, e in word_eqs:
    for a, b in re.findall(r'([XUM]\d+) \* ([XUM]\d+)', e): atoms.add((a, b))
limbs = sorted({t for n, e in word_eqs for t in re.findall(r'\b[XUM]\d+\b', e)})
res_names = [res[o] for o in qn]
Qv = ' + '.join(('2 ^ %d * %s' % (64 * i, v)) if i else v for i, v in enumerate(res_names))
Tdef = ' + '.join(('2 ^ %d * %s' % (om[0][n].bit_length() - 1, n)) if om[0][n] != 1 else n for n in invars if n in om[0])
invars = [n for n in invars if n not in ('x1cdm128',)]
allv = limbs + invars + [n for n, e in eqs]
out = 'import Fv256.Amd64.R4Seg0\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n'
out += 'theorem mulbb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by\n  exact Nat.mul_le_mul (by omega) (by omega)\n\n'
out += 'theorem s1_all (%s : Nat)\n' % ' '.join(allv)
for v in limbs: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
for n, e in word_eqs: out += '    (w_%s : %s = %s)\n' % (n, n, e)
for n, e in eqs: out += '    (h_%s : %s = %s)\n' % (n, n, e)
out += '    : (%s) * 2 ^ 320 ≤ (%s) ∧ (%s) < (%s) * 2 ^ 320 + 2 ^ 320 := by\n' % (Qv, Tdef, Tdef, Qv)
for a, b in sorted(atoms):
    out += '  have := mulbb %s %s b_%s b_%s\n  have := Nat.mul_comm %s %s\n' % (a, b, a, b, a, b)
exprs = [e for n, e in word_eqs] + [e for n, e in eqs]
out += '\n'.join(g4anf.anf(exprs, 's')) + '\n  omega\n\nend Fv256.Amd64.R4Seg\n'
open(ROOT + '/lean/Fv256/Amd64/R4ArithS1all.lean', 'w').write(out)
print(len(out), len(allv))
