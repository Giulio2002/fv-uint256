#!/usr/bin/env python3
"""g4s3.py: lean/Fv256/Proofs/Amd64/R4ArithS3.lean : the 5-limb subtraction unit 0x47f -> 0x4ac."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4eq, g4anf
ROOT = '/srv/fv-uint256-wf-r4'
eqs = dict(g4eq.eqs(0x47f, 0x4ac))
a = ['x47fm88', 'x47fm10', 'x47fm8', 'x47fm18', 'x47fm0']
b = ['x47frbx', 'x47frsi', 'x47fr8', 'x47frax', 'x47fr11']
outs = ['x4acrcx', 'x4acrdx', 'x4acrbx', 'x4acrsi', 'x4acr8']
D = '18446744073709551616'
out = 'import Fv256.Proofs.Amd64.R4Seg0\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n'
out += 'theorem bvsub_toNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = (a + 2 ^ 64 - b) % 2 ^ 64 := by\n  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]\n  omega\n\n'
vars_ = a + b + outs + ['x4acr9']
out += 'theorem s3_arith (%s : Nat)\n' % ' '.join(vars_)
for v in a + b: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
for n in outs + ['x4acr9']: out += '    (h_%s : %s = %s)\n' % (n, n, eqs[n])
def S(vs): return ' + '.join(v if i == 0 else '%d * %s' % (1 << (64 * i), v) for i, v in enumerate(vs))
T = 1 << 320
out += '    : %s = (%s + %d - (%s)) %% %d ∧ (x4acr9 = 0 ↔ %s ≤ %s) := by\n' % (S(outs), S(a), T, S(b), T, S(b), S(a))
out += '  have h1 : x4acrcx = (x47fm88 + 2 ^ 64 - x47frbx) %% 2 ^ 64 := by rw [h_x4acrcx]; exact bvsub_toNat _ _ b_x47fm88 b_x47frbx\n'.replace('%%', '%')
# mask: x4acr9 = 0 <-> cond
cond = re.match(r'\(if (.*) then 18446744073709551615#64 else 0#64\)\.toNat$', eqs['x4acr9']).group(1)
out += '  have hmask : (x4acr9 = 0 ↔ ¬ (%s)) := by\n    rw [h_x4acr9]\n    by_cases hc : %s <;> simp [hc]\n' % (cond, cond)
out += '  clear h_x4acr9 h_x4acrcx\n'
rest = [eqs[n] for n in outs[1:]] + [cond.split(' < ', 1)[1]]
out += '\n'.join(g4anf.anf(rest, 'q')) + '\n'
out += '  omega\n\nend Fv256.Amd64.R4Seg\n'
open(ROOT + '/lean/Fv256/Proofs/Amd64/R4ArithS3.lean', 'w').write(out)
