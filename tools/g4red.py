#!/usr/bin/env python3
"""g4red.py: lean/Fv256/Amd64/R4Arith.lean : theorem reduce4_arith (all chain facts -> dsum % M = x % M)."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4s1, g4s2, g4s3, g4bridge, g4arith, g4seg as g, g4hi
ROOT = '/srv/fv-uint256-wf-r4'
fine = [0x1cd, 0x1d9, 0x1f2, 0x20c, 0x236, 0x25b, 0x290, 0x2b5, 0x2e0, 0x2f8, 0x33e, 0x38b, 0x3ea, 0x429, 0x46b, 0x47f, 0x4ac]
units, cutnames = g4arith.chain_full(fine)
cidx = {c: i for i, c in enumerate(fine)}
def names_at(c): return cutnames[cidx[c]]
def local_names(c): return g.Ldef(c)[1]
invars = names_at(0x1cd)
alleqs = [(n, e) for u in units for n, e in u['eqs']]
newall = [n for n, e in alleqs]
hi = g4hi.hi_names()
def conv(e):
    def rl(mo):
        base = mo.group(1); off = int(mo.group(2) or 0)
        return {'3': 'X', '7': 'U', '1': 'M'}[base] + str(off // 8)
    e = re.sub(r'Arm64\.Memory\.readLE s\.mem \(BitVec\.toNat \(s\.regs (\d)\)(?: \+ (\d+))?\) 8', rl, e)
    return e.replace('BitVec.toNat (s.regs 0)', 'Z')
vdef = {}   # vK -> converted definition
xv = {}     # x1cd name -> vK
for n, (v, e) in hi.items():
    vdef[v] = conv(e); xv[n] = v
vs = sorted(vdef, key=lambda x: int(x[1:]))
limbs = ['X%d' % i for i in range(8)] + ['U%d' % i for i in range(5)] + ['M%d' % i for i in range(4)] + ['Z']
# ---- S2 / S3 name maps
n2f8 = local_names(0x2f8)
at2f8 = names_at(0x2f8)
m2 = dict(zip(n2f8, at2f8))
def map2(x): return m2.get(x, x)
n47 = local_names(0x47f); at47 = names_at(0x47f); m3 = dict(zip(n47, at47))
n4 = local_names(0x4ac); at4 = names_at(0x4ac)
def Sx(vs_): return ' + '.join(v if i == 0 else '%d * %s' % (1 << (64 * i), v) for i, v in enumerate(vs_))
# ---- lemma statement
out = ('import Fv256.Amd64.R4ArithS1F\nimport Fv256.Amd64.R4ArithS2\nimport Fv256.Amd64.R4ArithS3\nimport Fv256.Amd64.R4ArithBA\nimport Fv256.Amd64.R4Value\n\n'
       'set_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\nopen Fv256.F\n\n')
out += 'theorem r4_comb (P Psi T Q N : Nat) (h : Q * N ≤ Psi) (h\' : Psi < Q * N + N) (hb : Psi = T) (ht1 : T ≤ P) (ht2 : P < T + N) :\n    Q * N ≤ P ∧ P < Q * N + 2 * N := by omega\n\n'
d = ['d%d' % i for i in range(5)]
allp = limbs + vs + invars + newall + d
out += 'theorem reduce4_arith (%s : Nat)\n' % ' '.join(allp)
for v in limbs[:-1]: out += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
out += '    (hM3 : 1 ≤ M3)\n    (hRW : RecipWeak (M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3) (U0 + 2 ^ 64 * U1 + 2 ^ 128 * U2 + 2 ^ 192 * U3 + 2 ^ 256 * U4))\n'
for v in vs: out += '    (hv_%s : %s = %s)\n' % (v, v, vdef[v])
for n in invars: out += '    (hx_%s : %s = %s %% 18446744073709551616)\n' % (n, n, xv[n])
for n, e in alleqs: out += '    (h_%s : %s = %s)\n' % (n, n, e)
act_r9 = at4[n4.index('x4acr9')]
M_n = [at4[n4.index('x4acm60')], at4[n4.index('x4acm68')], at4[n4.index('x4acr12')], at4[n4.index('x4acrdi')]]
Mn = ' + '.join(v if i == 0 else '%d * %s' % (1 << (64 * i), v) for i, v in enumerate(M_n))
C4 = ' + '.join(at4[n4.index(r)] if i == 0 else '%d * %s' % (1 << (64 * i), at4[n4.index(r)]) for i, r in enumerate(['x4acrcx', 'x4acrdx', 'x4acrbx', 'x4acrsi', 'x4acr8']))
dsum = ' + '.join(d[0:1] + ['%d * %s' % (1 << (64 * i), d[i]) for i in range(1, 5)])
out += '    (hd : %s = (%s + (if %s = 0 then 0 else %s)) %% %d)\n' % (dsum, C4, act_r9, Mn, 1 << 320)
Xv = ' + '.join(['X0'] + ['%d * X%d' % (1 << (64 * i), i) for i in range(1, 8)])
Mv = ' + '.join(['M0'] + ['%d * M%d' % (1 << (64 * i), i) for i in range(1, 4)])
out += '    : %s = %s ∧ (%s) %% (%s) = (%s) %% (%s) := by\n' % (Mn, Mv, dsum, Mn, Xv, Mn)

# ---------------- proof
P = []
# bounds of x1cd names and of all `% 2^64` equation vars
bnew = [n for n in newall if n not in ('x4acrcx', 'x4acr9')]
for n in invars: P.append('  have b_%s := bdm hx_%s' % (n, n))
for n in bnew: P.append('  have b_%s := bdm h_%s' % (n, n))
# word definitions
for n in g4s1.wv + [x for x in g4bridge.wv if x not in g4s1.wv]:
    P.append('  have w_%s : %s = %s := by rw [hx_%s, hv_%s]' % (n, n, g4s1.words[n], n, xv[n]))
# limb words (needed for the conversions)
_lw = [n for n in invars if '*' not in hi[n][1] and 'regs 0' not in hi[n][1]]
for n in _lw:
    if n not in g4s1.wv and n not in g4bridge.wv:
        P.append('  have w_%s : %s = (%s) %% 18446744073709551616 := by rw [hx_%s, hv_%s]' % (n, n, vdef[xv[n]], n, xv[n]))
# S1
a1 = ' '.join(g4s1.allf + ['b_' + v for v in g4s1.limbs + g4s1.free] + ['w_' + n for n in g4s1.wv] + ['h_' + n for n, e in g4s1.alleqs])
P.append('  have s1 := s1_final %s' % a1)
a2 = ' '.join(g4bridge.limbs + g4bridge.wv + ['b_' + v for v in g4bridge.limbs] + ['w_' + n for n in g4bridge.wv])
P.append('  have br := bridgeA %s' % a2)
# trunc_q
a_ = ['X%d' % (3 + i) for i in range(5)]; u_ = ['U%d' % j for j in range(5)]
Pn = '(%s) * (%s)' % (' + '.join([a_[0]] + ['2 ^ %d * %s' % (64 * i, a_[i]) for i in range(1, 5)]), ' + '.join([u_[0]] + ['2 ^ %d * %s' % (64 * i, u_[i]) for i in range(1, 5)]))
Tt = g4bridge.T
P.append('  have tq := Fv256.F.trunc_q (%s) (%s) %s %s %s %s' % (Pn, g4bridge.Psi0, ' '.join(a_), ' '.join(u_), ' '.join('b_' + v for v in a_ + u_), 'rfl br'))
# S2
args2 = ' '.join(map2(v) for v in g4s2.allv + [])
b2 = ' '.join('b_' + map2(v) for v in g4s2.invars)
h2 = ' '.join('h_' + n for n, e in g4s2.eqs)
P.append('  have s2 := s2_arith %s %s %s' % (args2, b2, h2))
# S3
a3v = g4s3.a; b3v = g4s3.b
vars3 = [m3.get(v, v) for v in a3v + b3v] + g4s3.outs + ['x4acr9']
P.append('  have s3 := s3_arith %s %s %s' % (' '.join(vars3), ' '.join('b_' + m3.get(v, v) for v in a3v + b3v), ' '.join('h_' + n for n in g4s3.outs + ['x4acr9'])))

# ---------------- conversions + final
limb_words = [n for n in invars if '*' not in hi[n][1] and 'regs 0' not in hi[n][1]]
clr = ['hv_' + v for v in vs] + ['hx_' + n for n in invars] + ['h_' + n for n in newall if n != 'x33er12'] + ['b_' + n for n in invars + bnew]
clr += ['w_' + n for n in (g4s1.wv + [x for x in g4bridge.wv if x not in g4s1.wv]) if n not in limb_words]
P.append('  clear %s' % ' '.join(clr))
# keep w_ for limb words that are not in wv: define now
Qs2 = ' + '.join(map2(g4s2.q[i]) if i == 0 else '2 ^ %d * %s' % (64 * i, map2(g4s2.q[i])) for i in range(5))
Ms2 = ' + '.join(map2(g4s2.m[i]) if i == 0 else '2 ^ %d * %s' % (64 * i, map2(g4s2.m[i])) for i in range(4))
Bs2 = ' + '.join(map2(g4s2.res[o]) if i == 0 else '2 ^ %d * %s' % (64 * i, map2(g4s2.res[o])) for i, o in enumerate(g4s2.outs))
Bs3 = Sx([m3.get(v, v) for v in g4s3.b])
A3 = Sx([m3.get(v, v) for v in g4s3.a])
R13 = Sx(g4s3.outs)
Av = ' + '.join(['X0'] + ['%d * X%d' % (1 << (64 * i), i) for i in range(1, 5)])
N = 1 << 320
P.append('  have hb : %s = %s := by omega' % (g4s1.Psi0, g4bridge.Psi0))
P.append('  have c1 := r4_comb (%s) (%s) (%s) (%s) (2 ^ 320) s1.1 s1.2 hb tq.1 tq.2' % (Pn, g4s1.Psi0, g4bridge.Psi0, g4s1.Qv))
P.append('  have hQ : %s = %s := by omega' % (g4s1.Qv, Qs2))
P.append('  have hMA : %s = %s := by omega' % (Ms2, Mv))
P.append('  have hA : %s = %s := by omega' % (A3, Av))
P.append('  have hBB : %s = %s := by omega' % (Bs3, Bs2))
P.append('  have hMn : %s = %s := by omega' % (Mn, Mv))
P.append('  rw [hQ] at c1')
P.append('  rw [hMA] at s2')
P.append('  rw [hA, hBB] at s3')
P.append('  rw [hMn] at hd')
P.append('  have fin := r4_value X0 X1 X2 X3 X4 X5 X6 X7 U0 U1 U2 U3 U4 M0 M1 M2 M3 (%s) (%s) (%s) %s (%s) %s hM3 hRW c1.1 c1.2 s2 s3.1 s3.2 hd' % (Qs2, Bs2, R13, act_r9, dsum, ' '.join('b_' + v for v in limbs[:-1])))
P.append('  exact ⟨hMn, by rw [hMn]; exact fin⟩')
open(ROOT + '/lean/Fv256/Amd64/R4Arith.lean', 'w').write(out + '\n'.join(P) + '\n\nend Fv256.Amd64.R4Seg\n')
