#!/usr/bin/env python3
"""g4bridge.py: lean/Fv256/Proofs/Amd64/R4ArithBA.lean : the weighted A-words equal the truncated partial-product sum T of MulModTrunc.trunc_q."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4rows, g4hi, g4anf
ROOT = '/srv/fv-uint256-wf-r4'
cuts = [0x1cd, 0x1d9, 0x1f2, 0x20c, 0x236, 0x25b, 0x290, 0x2b5, 0x2e0, 0x2f8]
qn = ['x2f8rax', 'x2f8rdx', 'x2f8rcx', 'x2f8r10', 'x2f8r8']
fw = {n: 1 << (320 + 64 * i) for i, n in enumerate(qn)}
import g4w2, g4chain
om = g4w2.weights_chain(cuts, fw)
hi = g4hi.hi_names()
def conv(e):
    def rl(mo):
        base = mo.group(1); off = int(mo.group(2) or 0)
        return {'3': 'X', '7': 'U', '1': 'M'}[base] + str(off // 8)
    return re.sub(r'Arm64\.Memory\.readLE s\.mem \(BitVec\.toNat \(s\.regs (\d)\)(?: \+ (\d+))?\) 8', rl, e)
words = {n: '(%s) %% 18446744073709551616' % conv(e) for n, (v, e) in hi.items() if 'regs 0' not in e}
wv = [n for n in words if n in om[0]]
Psi0 = ' + '.join((n if om[0][n] == 1 else '%d * %s' % (om[0][n], n)) for n in wv)
a = ['X%d' % (3 + i) for i in range(5)]; u = ['U%d' % j for j in range(5)]
def P(i, j): return '(%s * %s)' % (a[i], u[j])
a_ = ['X%d' % (3 + i) for i in range(5)]
(a0, a1, a2, a3, a4) = a_
(u0, u1, u2, u3, u4) = u
T = ('2 ^ 256 * ((%s * %s / 2 ^ 64) + (%s * %s / 2 ^ 64) + (%s * %s / 2 ^ 64) + (%s * %s / 2 ^ 64)) +\n      2 ^ 256 * (%s * %s + %s * %s + %s * %s + %s * %s + %s * %s) +\n      2 ^ 320 * (%s * %s + %s * %s + %s * %s + %s * %s) +\n      2 ^ 384 * (%s * %s + %s * %s + %s * %s) +\n      2 ^ 448 * (%s * %s + %s * %s) +\n      2 ^ 512 * (%s * %s)'
     % (a3, u0, a2, u1, a1, u2, a0, u3, a4, u0, a3, u1, a2, u2, a1, u3, a0, u4, a4, u1, a3, u2, a2, u3, a1, u4, a4, u2, a3, u3, a2, u4, a4, u3, a3, u4, a4, u4))
limbs = sorted({t for n in wv for t in re.findall(r'\b[XUM]\d+\b', words[n])} | set(a) | set(u))
atoms = sorted({m for n in wv for m in re.findall(r'([XUM]\d+) \* ([XUM]\d+)', words[n])} | {(a[i], u[j]) for i in range(5) for j in range(5)})
out = 'import Fv256.Proofs.Amd64.R4Seg0\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n'
out += 'theorem mulb2 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 := by\n  have := Nat.mul_lt_mul\'\' ha hb\n  rwa [← Nat.pow_add] at this\n\n'
out += 'theorem bridgeA (%s : Nat)\n' % ' '.join(limbs + wv)
for v in limbs: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
for n in wv: out += '    (w_%s : %s = %s)\n' % (n, n, words[n])
out += '    : %s = %s := by\n' % (Psi0, T)
for x, y in atoms:
    out += '  have := mulb2 %s %s b_%s b_%s\n  have := Nat.mul_comm %s %s\n' % (x, y, x, y, x, y)
out += '\n'.join(g4anf.anf([words[n] for n in wv] , 'p')) + '\n'
# T's divisions need ANF too: generalise them via the same helper on a pseudo expression
out += '  omega\n\nend Fv256.Amd64.R4Seg\n'
open(ROOT + '/lean/Fv256/Proofs/Amd64/R4ArithBA.lean', 'w').write(out)
print(len(out))
