#!/usr/bin/env python3
"""g4s1.py: generate lean/Fv256/Proofs/Amd64/R4ArithS1b.lean : Q * 2^320 <= T < Q * 2^320 + 2^320 for cuts 1cd .. 2f8 (rows + capacities)."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4rows, g4hi, g4anf, g4chain
import g4seg as g
ROOT = '/srv/fv-uint256-wf-r4'
cuts = [0x1cd, 0x1d9, 0x1f2, 0x20c, 0x236, 0x25b, 0x290, 0x2b5, 0x2e0, 0x2f8]
qn = ['x2f8rax', 'x2f8rdx', 'x2f8rcx', 'x2f8r10', 'x2f8r8']
fw = {n: 1 << (320 + 64 * i) for i, n in enumerate(qn)}
dropped = {7: lambda ia, nA: '%d * ((%s + %s) %% 18446744073709551616)' % (1 << 256, ia[nA.index('x2b5r11')], ia[nA.index('x2b5ma8')])}
rtext, info, om, units = g4rows.rows(cuts, fw, 's1', dropped)
hi = g4hi.hi_names()
def conv(e):
    def rl(mo):
        base = mo.group(1); off = int(mo.group(2) or 0)
        return {'3': 'X', '7': 'U', '1': 'M'}[base] + str(off // 8)
    return re.sub(r'Arm64\.Memory\.readLE s\.mem \(BitVec\.toNat \(s\.regs (\d)\)(?: \+ (\d+))?\) 8', rl, e)
words = {n: '(%s) %% 18446744073709551616' % conv(e) for n, (v, e) in hi.items() if 'regs 0' not in e}
wv = [n for n in words if n in om[0]]          # words that carry a weight
atoms = sorted({m for n in wv for m in re.findall(r'([XUM]\d+) \* ([XUM]\d+)', words[n])})
limbs = sorted({t for n in wv for t in re.findall(r'\b[XUM]\d+\b', words[n])})
out = 'import Fv256.Proofs.Amd64.R4Seg0\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n'
out += 'theorem mulbb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by\n  exact Nat.mul_le_mul (by omega) (by omega)\n\n'
out += rtext
Psi0 = info[0]['lhs']
# capacity lemmas
for k, i in enumerate(info):
    cons_words = sorted({w for kk in range(k + 1) for w in info[kk]['cons'] if w in wv})
    vars_k = list(dict.fromkeys(i['in_act']))
    allv = list(dict.fromkeys(limbs + wv + vars_k))
    th = 'theorem s1_cap%d (%s : Nat)\n' % (k, ' '.join(allv))
    for v in limbs: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
    for n in wv: th += '    (w_%s : %s = %s)\n' % (n, n, words[n])
    if k > 0: th += '    (hE : %s ≤ %s)\n' % (i['lhs'], Psi0)
    th += '    : %s < %d := by\n' % (i['S'], 1 << i['cap'])
    for a, b in atoms: th += '  have := mulbb %s %s b_%s b_%s\n  have := Nat.mul_comm %s %s\n' % (a, b, a, b, a, b)
    th += '\n'.join(g4anf.anf([words[n] for n in wv], 'c%d' % k)) + '\n  omega\n\n'
    out += th

# ---- final composition (3 stages + glue, each below the default heartbeat budget)
res_q = units[-1]['outargs']
_, nZ = g.Ldef(cuts[-1])
qact = [res_q[nZ.index(q)] for q in qn]
Qv = ' + '.join(('%d * %s' % (1 << (64 * j), v)) if j else v for j, v in enumerate(qact))
free = [v for v in info[0]['in_act'] if v not in wv]
stages = [(0, 3), (3, 6), (6, 9)]
D7 = dropped[7](info[7]['in_act'], g.Ldef(cuts[7])[1])
fin = ''
stage_args = []
for si, (a, b) in enumerate(stages):
    rows_ = info[a:b]
    neweq = [(n, e) for ii in rows_ for n, e in ii['eqs']]
    newn = [n for n, e in neweq]
    allv_ = list(dict.fromkeys(limbs + wv + free + [v for ii in rows_ for v in ii['allv']]))
    # bounded-by-hyp variables: in-vars of the stage that are not words/limbs/free and not defined in the stage
    ext = [v for v in allv_ if v not in limbs and v not in wv and v not in free and v not in newn]
    hyps = ['b_' + v for v in limbs + free + ext]
    concl_eq = '%s = %s%s' % (rows_[0]['lhs'], rows_[-1]['rhs'], (' + ' + D7) if a <= 7 < b else '')
    concl = concl_eq + (' ∧ %s ≤ %s' % (info[b]['lhs'], Psi0) if b < len(info) else '')
    th = 'theorem s1_st%d (%s : Nat)\n' % (si, ' '.join(allv_))
    for v in limbs + free + ext: th += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
    for n in wv: th += '    (w_%s : %s = %s)\n' % (n, n, words[n])
    for n, e in neweq: th += '    (h_%s : %s = %s)\n' % (n, n, e)
    if a > 0: th += '    (hE%d : %s ≤ %s)\n' % (a, info[a]['lhs'], Psi0)
    th += '    : %s := by\n' % concl
    for n in newn: th += '  have b_%s := bdm h_%s\n' % (n, n)
    for n in wv: th += '  have b_%s := bdm w_%s\n' % (n, n)
    for k in range(a, b):
        ii = info[k]
        vars_k = list(dict.fromkeys(ii['in_act']))
        capargs = list(dict.fromkeys(limbs + wv + vars_k))
        args = ' '.join(capargs + ['b_' + v for v in limbs] + ['w_' + n for n in wv] + (['hE%d' % k] if k > 0 else []))
        th += '  have c%d := s1_cap%d %s\n' % (k, k, args)
        rargs = ' '.join(ii['allv'] + ['b_' + v for v in ii['in_act']] + ['h_' + n for n, e in ii['eqs']] + ['c%d' % k])
        th += '  have r%d := s1_r%d %s\n' % (k, k, rargs)
        if k + 1 < b:
            if k == 0: prf = 'Nat.le_of_eq r0.symm'
            elif k == 7: prf = 'Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_of_eq r7.symm) hE7)'
            else: prf = 'Nat.le_trans (Nat.le_of_eq r%d.symm) hE%d' % (k, k)
            th += '  have hE%d : %s ≤ %s := %s\n' % (k + 1, info[k + 1]['lhs'], Psi0, prf)
    # conclusion
    rs = ['r%d' % k for k in range(a, b)]
    if b < len(info):
        k = b - 1
        if k == 7: prf = 'Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_of_eq r7.symm) hE7)'
        elif k == 0: prf = 'Nat.le_of_eq r0.symm'
        else: prf = 'Nat.le_trans (Nat.le_of_eq r%d.symm) hE%d' % (k, k)
        lastle = ', ' + prf
    else: lastle = ''
    th += '  clear %s\n' % ' '.join(['c%d' % k for k in range(a, b)] + ['b_' + v for v in limbs + free + ext + wv + newn] + ['w_' + n for n in wv] + ['h_' + n for n, e in neweq])
    # equality chain by transitivity (rhs_k and lhs_{k+1} are syntactically equal)
    ch = None; seen7 = False
    for k in range(a, b):
        if ch is None: ch = 'r%d' % k
        elif k - 1 == 7:
            ch = '(%s).trans (congrArg (fun x => x + %s) r%d)' % (ch, D7, k)
        else:
            ch = '(%s).trans r%d' % (ch, k)
    th += ('  exact ⟨%s%s⟩\n\n' % (ch, lastle)) if lastle else ('  exact %s\n\n' % ch)
    fin += th
    stage_args.append((si, a, b, allv_, ext, newn, neweq))
# top-level glue
alleqs = [(n, e) for ii in info for n, e in ii['eqs']]
newall = [n for n, e in alleqs]
allf = list(dict.fromkeys(limbs + wv + free + newall))
top = 'theorem s1_final (%s : Nat)\n' % ' '.join(allf)
for v in limbs + free: top += '    (b_%s : %s < 2 ^ 64)\n' % (v, v)
for n in wv: top += '    (w_%s : %s = %s)\n' % (n, n, words[n])
for n, e in alleqs: top += '    (h_%s : %s = %s)\n' % (n, n, e)
T320 = 1 << 320
top += '    : (%s) * %d ≤ %s ∧ %s < (%s) * %d + %d := by\n' % (Qv, T320, Psi0, Psi0, Qv, T320, T320)
for n in newall: top += '  have b_%s := bdm h_%s\n' % (n, n)
for n in wv: top += '  have b_%s := bdm w_%s\n' % (n, n)
for si, a, b, allv_, ext, newn, neweq in stage_args:
    args = ' '.join(allv_ + ['b_' + v for v in limbs + free + ext] + ['w_' + n for n in wv] + ['h_' + n for n, e in neweq] + (['hE%d' % a] if a > 0 else []))
    top += '  have s%d := s1_st%d %s\n' % (si, si, args)
    if b < len(info):
        top += '  have hE%d := s%d.2\n' % (b, si)
top += '  clear %s\n' % ' '.join(['b_' + v for v in limbs + free + wv + newall] + ['w_' + n for n in wv] + ['h_' + n for n in newall] + ['hE%d' % b for si, a, b, *_ in stage_args if b < len(info)])
top += '  omega\n\n'
fin += top
fin_text = fin
open(ROOT + '/lean/Fv256/Proofs/Amd64/R4ArithS1.lean', 'w').write(out + 'end Fv256.Amd64.R4Seg\n')
open(ROOT + '/lean/Fv256/Proofs/Amd64/R4ArithS1F.lean', 'w').write('import Fv256.Proofs.Amd64.R4ArithS1\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\ntheorem bdm {v E : Nat} (h : v = E % 18446744073709551616) : v < 2 ^ 64 := by rw [h]; exact Nat.mod_lt _ (by decide)\n\n' + fin_text + 'end Fv256.Amd64.R4Seg\n')
print(len(out), len(wv), len(atoms))
