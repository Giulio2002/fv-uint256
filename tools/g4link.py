#!/usr/bin/env python3
"""g4link.py: linkA lemma: PostA s S  ->  L<cut> s S (live witnesses) + R4Regs + R4Mem  (witnesses are the A-variables mod 2^64).
usage: g4link.py CUT_HEX  -> writes lean/Fv256/Amd64/R4LinkA.lean in /srv/fv-uint256-wf-r4"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import g4seg as g
cut = int(sys.argv[1], 16)
ROOT = g.ROOT
t = open(ROOT + '/lean/Fv256/Amd64/ReduceSegA.lean').read()
i = t.index('def PostA'); j = t.index('theorem segA ', i)
d = t[i:j]
body = d[d.index('∃ ') :]
vars_, rest = body[2:].split(', ', 1)[0], body[2:].split(', ', 1)[1]
vars_ = vars_.split()
# split top-level conjuncts
def split_conj(s):
    out = []; depth = 0; cur = ''; k = 0
    while k < len(s):
        c = s[k]
        if c == '(': depth += 1
        if c == ')': depth -= 1
        if depth == 0 and s.startswith(' ∧ ', k):
            out.append(cur.strip()); cur = ''; k += 3; continue
        cur += c; k += 1
    out.append(cur.strip()); return out
cs = split_conj(rest.strip())
assert cs[-2].startswith('RegsA') and cs[-1].startswith('MemFrame'), cs[-2:]
facts = cs[:-2]
regmap = {}; memmap = {}
for n, f in enumerate(facts):
    m = re.fullmatch(r"\(S'\.regs (\d+) = BitVec\.ofNat 64 (v\d+)\)", f)
    if m: regmap[int(m.group(1))] = (m.group(2), n); continue
    m = re.fullmatch(r"\(S'\.mem\.readLE \(BitVec\.toNat \(s\.regs 4\) (-|\+) (\d+)\) 8 = (v\d+) % 2 \^ 64\)", f)
    if m: memmap[(-1 if m.group(1) == '-' else 1) * int(m.group(2))] = (m.group(3), n)
its = g.items(cut)
_, names = g.Ldef(cut)
wit = []; leaves = []
for (k, key), nm in zip(its, names):
    if k == 'r':
        v, n = regmap[g.RIDX[key]]
        wit.append('%s %% 18446744073709551616' % v)
        leaves.append('rw [ofNat_mod64]; exact f%d' % n)
    else:
        off = key - 288
        v, n = memmap[off]
        wit.append('%s %% 18446744073709551616' % v)
        leaves.append('exact f%d' % n)
    leaves.append('exact Nat.mod_lt _ (by decide)')
out = ['import Fv256.Amd64.R4Live', 'import Fv256.Amd64.ReduceSegA', '', 'open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic', 'open Fv256.Amd64.ReduceSpec Fv256.Amd64.ReduceSegA', '',
       'namespace Fv256.Amd64.R4Seg', '']
vs = ' '.join(vars_)
eqs = [(nm, w) for nm, w in zip(names, wit)]
defs = [(m.group(1), m.group(2)) for f in facts for m in [re.fullmatch(r"\((v\d+) = (.*)\)", f)] if m]
out.append('/-- the Phase A values (as ofNat witnesses) satisfy the live state at the cut -/')
out.append('theorem linkA (s S : State) (h : PostA s S) :')
out.append('    ∃ %s %s, L%x s S %s ∧ R4Regs s S ∧ R4Mem s S.mem ∧' % (vs, ' '.join(names), cut, ' '.join(names)))
out.append('      (%s) ∧' % ' ∧ '.join('%s = %s' % (nm, w) for nm, w in eqs))
out.append('      (%s) := by' % ' ∧ '.join('%s = %s' % (a, b) for a, b in defs))
out.append('  unfold PostA at h')
out.append('  obtain ⟨%s, hh⟩ := h' % ', '.join(vars_))
out.append('  obtain ⟨%s, hR, hF⟩ := hh' % ', '.join('f%d' % n for n in range(len(facts))))
out.append('  refine ⟨%s, %s, ?_, ?_, ?_, ?_, ?_⟩' % (', '.join(vars_), ', '.join(wit)))
out.append('  · unfold L%x\n    and_intros' % cut)
for l in leaves: out.append('    · ' + l)
out.append('  · exact hR')
out.append('  · exact hF')
out.append('  · and_intros <;> rfl')
out.append('  · and_intros' + ''.join('\n    · exact f%d' % n for n, f in enumerate(facts) if re.fullmatch(r"\(v\d+ = .*\)", f)))
out.append('\nend Fv256.Amd64.R4Seg\n')
open(ROOT + '/lean/Fv256/Amd64/R4LinkA.lean', 'w').write('\n'.join(out))
print(len(facts), len(vars_))
