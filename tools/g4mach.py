#!/usr/bin/env python3
"""g4mach.py: lean/Fv256/Proofs/Amd64/R4Reduce.lean : theorem reduce4_machine (entry -> return, R4Post)."""
import sys, re, os
sys.path.insert(0, os.path.dirname(__file__))
import g4red as R, g4seg as g
ROOT = R.ROOT
# defs order in linkA = order of "v = expr" facts in PostA
t = open(ROOT + '/lean/Fv256/Proofs/Amd64/ReduceSegA.lean').read()
i = t.index('def PostA'); j = t.index('theorem segA ', i); d = t[i:j]
body = d[d.index('∃ '):]
rest = body[2:].split(', ', 1)[1]
cs = []; depth = 0; cur = ''; k = 0
while k < len(rest):
    c = rest[k]
    if c == '(': depth += 1
    if c == ')': depth -= 1
    if depth == 0 and rest.startswith(' ∧ ', k): cs.append(cur.strip()); cur = ''; k += 3; continue
    cur += c; k += 1
cs.append(cur.strip())
vorder = [m.group(1) for f in cs for m in [re.fullmatch(r"\((v\d+) = (.*)\)", f)] if m]
assert len(vorder) == 47
def rd(base, i): return 's.mem.readLE (BitVec.toNat (s.regs %d)%s) 8' % (base, '' if i == 0 else ' + %d' % (8 * i))
X = [rd(3, i) for i in range(8)]; U = [rd(7, i) for i in range(5)]; M = [rd(1, i) for i in range(4)]
Z = 'BitVec.toNat (s.regs 0)'
lim = ['(%s)' % e for e in X + U + M + [Z]]
vs = R.vs; invars = R.invars; newall = R.newall
out = ('import Fv256.Proofs.Amd64.R4Arith\nimport Fv256.Amd64.R4Branch\nimport Fv256.Amd64.R4LinkA\nimport Fv256.Amd64.R4G.C_1cd_4ac\n\n'
       'open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic\nopen Fv256.Amd64.ReduceSpec Fv256.Amd64.ReduceSegA\n\nset_option exponentiation.threshold 700\nnamespace Fv256.Amd64.R4Seg\n\n')
out += '''theorem readLE_40' (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 40 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 := by
  rw [show 40 = 32 + 8 from rfl, Janus.Arm64.Memory.readLE_add, Fv256.Util.readLE_32]

theorem readLE_64' (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 64 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 +
      2 ^ 256 * m.readLE (a + 32) 8 + 2 ^ 320 * m.readLE (a + 40) 8 + 2 ^ 384 * m.readLE (a + 48) 8 + 2 ^ 448 * m.readLE (a + 56) 8 := by
  rw [show 64 = 32 + 32 from rfl, Janus.Arm64.Memory.readLE_add, Fv256.Util.readLE_32, Fv256.Util.readLE_32 m (a + 32)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

'''
out += 'set_option maxHeartbeats 64000000 in\nset_option maxRecDepth 200000 in\n'
out += 'theorem reduce4_machine (s : State) (hpc : s.rip = BitVec.ofNat 64 r4Entry) (hpre : R4Pre s) :\n    ReachesRet Fv256.ReduceProg.program (retAddrOf s) s (R4Post s) := by\n'
L = []
L.append('  have hpre0 := hpre')
L.append('  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hpre0')
L.append('  refine Fv256.SegCompose.seg_trans (segA s hpc hpre) ?_')
L.append('  intro S1 hpc1 hA')
L.append('  obtain ⟨%s, %s, hh⟩ := linkA s S1 hA' % (', '.join(vorder), ', '.join(invars)))
L.append('  obtain ⟨hL, hR1, hM1, hLE⟩ := hh')
L.append('  obtain ⟨hxeq, hveq⟩ := hLE')
L.append('  obtain ⟨%s⟩ := hxeq' % ', '.join('hx_' + n for n in invars))
L.append('  obtain ⟨%s⟩ := hveq' % ', '.join('hv_' + v for v in vorder))
L.append('  refine Fv256.SegCompose.seg_trans (c_1cd_4ac s S1 hpc1 hpre hR1 hM1 %s hL) ?_' % ' '.join(invars))
L.append('  intro S2 hpc2 hq')
L.append('  unfold PC_1cd_4ac at hq')
L.append('  obtain ⟨%s, hq2⟩ := hq' % ', '.join(newall))
L.append('  obtain ⟨hLz, hEz, hRz, hMz⟩ := hq2')
L.append('  obtain ⟨%s⟩ := hEz' % ', '.join('h_' + n for n in newall))
L.append('  have hz : x1cdm128 = (s.regs 0).toNat := by rw [hx_x1cdm128, hv_v13]; exact Nat.mod_eq_of_lt (s.regs 0).isLt')
act4 = R.act4 if hasattr(R, 'act4') else [R.at4[i] for i in range(12)]
L.append('  refine Fv256.SegCompose.seg_trans (branch s hpre S2 hpc2 hRz hMz %s hLz hz) ?_' % ' '.join(R.at4))
L.append('  intro S3 hpc3 hb')
L.append('  obtain ⟨d0, d1, d2, d3, d4, hTI, hdsum⟩ := hb')
open(ROOT + '/lean/Fv256/Proofs/Amd64/R4Reduce.lean', 'w').write(out + '\n'.join(L) + '\n  sorry\n\nend Fv256.Amd64.R4Seg\n')
print(len(out))
