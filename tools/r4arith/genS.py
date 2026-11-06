import re,json
BL='18446744073709551616'
D='/srv/fv-uint256-wB3/lean/Fv256/Arm64/R4G/'
def pdef(f,P):
    t=open(D+f+'.lean').read()
    i=t.index('def '+P); j=t.index('set_option maxHeartbeats',i)
    return t[i:j]
def newvars_and_hyps(f,P,L):
    d=pdef(f,P)
    body=d.split(':=\n',1)[1].strip()
    ex=re.match(r'∃ ([^,]*), (.*)$',body,re.S)
    nv=ex.group(1).split()
    rest=ex.group(2)
    parts=rest.split(' ∧ ')
    hs=[]
    for p in parts[1:]:
        m=re.match(r'(x[0-9a-f]+[rm][0-9]+) = ',p)
        if m and m.group(1) in nv: hs.append('h_'+m.group(1))
    return nv,hs
ob=open(D+'c_20_1d8.obtain').read()
mm=re.search(r'obtain ⟨(.*)⟩ := h',ob)
names=[x.strip() for x in mm.group(1).split(',')]
iL=names.index('hLz')
vars1=names[:iL]; hyps1=names[iL+1:-2]
sel=json.load(open('q_eqs.json'))
qn=[n for n,_ in sel]
lines=[]
A=lambda k:'s.mem.readLE (BitVec.toNat (s.regs 1) + %d) 8'%(24+8*k)
U=lambda j:'s.mem.readLE (BitVec.toNat (s.regs 3)) 8' if j==0 else 's.mem.readLE (BitVec.toNat (s.regs 3) + %d) 8'%(8*j)
out='''import Fv256.Arm64.R4Pro
import Fv256.Arm64.R4G.C_20_1d8
import Fv256.Arm64.R4G.G_1d8_284
import Fv256.Arm64.R4G.G_284_2b4
import Fv256.Arm64.R4G.G_2b4_2f4
import Fv256.Arm64.R4LoopRun
import Fv256.Arm64.R4Q
import Fv256.Arm64.R4Qm
import Fv256.Arm64.R4Qr
import Fv256.Arm64.R4Glue

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec Fv256.Arm64.R4Nat

namespace Fv256.Arm64.R4Seg

theorem readLE_64 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 64 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 +
      2 ^ 256 * m.readLE (a + 32) 8 + 2 ^ 320 * m.readLE (a + 40) 8 + 2 ^ 384 * m.readLE (a + 48) 8 + 2 ^ 448 * m.readLE (a + 56) 8 := by
  rw [show 64 = 8 + 56 from rfl, Janus.Arm64.Memory.readLE_add, show 56 = 8 + 48 from rfl,
    Janus.Arm64.Memory.readLE_add, show 48 = 8 + 40 from rfl, Janus.Arm64.Memory.readLE_add, show 40 = 8 + 32 from rfl,
    Janus.Arm64.Memory.readLE_add, show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem readLE_40 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 40 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 +
      2 ^ 256 * m.readLE (a + 32) 8 := by
  rw [show 40 = 8 + 32 from rfl, Janus.Arm64.Memory.readLE_add, show 32 = 8 + 24 from rfl,
    Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl, Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl,
    Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem r4_summary : R4Summary := by
  intro s hpc hs
  have hs0 := hs
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hbz, hbx, hbm, hbu, hm3, hmu⟩ := hs0
  refine Fv256.Arm64.SegCompose.seg_trans (r4_pro s hpc hs) ?_
  intro S0 hpc0 hq0
  obtain ⟨hL0, hR0, hM0⟩ := hq0
  refine Fv256.Arm64.SegCompose.seg_trans (c_20_1d8 s S0 hpc0 hs hR0 hM0 _ _ _ hL0 rfl rfl rfl) ?_
  intro S1 hpc1 hq1
  unfold PC_20_1d8 at hq1
  obtain ⟨%s, hq1⟩ := hq1
  obtain ⟨hL1, %s, hR1, hM1⟩ := hq1
''' % (', '.join(vars1),', '.join(hyps1))
# 1d8 -> 284
nv2,h2=newvars_and_hyps('G_1d8_284','P_1d8_284','L284')
out+='''  refine Fv256.Arm64.SegCompose.seg_trans (g_1d8_284 s S1 hpc1 hs hR1 hM1 x114r1 x114r2 x1d8r3 x1d8r4 x114r5 x1d8r6 x1d8r7 x1d8r9 x114m8 x114m16 x114m24 x114m32 x114m64 x114m72 x114m120 hL1) ?_
  intro S2 hpc2 hq2
  unfold P_1d8_284 at hq2
  obtain ⟨%s, hq2⟩ := hq2
  obtain ⟨hL2, %s, hR2, hM2⟩ := hq2
'''%(', '.join(nv2),', '.join(h2))
nv3,h3=newvars_and_hyps('G_284_2b4','P_284_2b4','L2b4')
out+='''  refine Fv256.Arm64.SegCompose.seg_trans (g_284_2b4 s S2 hpc2 hs hR2 hM2 x114r1 x114r2 x284r3 x284r4 x284r5 x284r6 x114m64 x284r26 x114m8 x114m16 x114m24 x114m32 x114m72 x114m120 hL2) ?_
  intro S3 hpc3 hq3
  unfold P_284_2b4 at hq3
  obtain ⟨%s, hq3⟩ := hq3
  obtain ⟨hL3, %s, hR3, hM3⟩ := hq3
'''%(', '.join(nv3),', '.join(h3))
nv4,h4=newvars_and_hyps('G_2b4_2f4','P_2b4_2f4','L2f4')
out+='''  refine Fv256.Arm64.SegCompose.seg_trans (g_2b4_2f4 s S3 hpc3 hs hR3 hM3 x114r1 x114r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x114m64 x114m72 hL3) ?_
  intro S4 hpc4 hq4
  unfold P_2b4_2f4 at hq4
  obtain ⟨%s, hq4⟩ := hq4
  obtain ⟨hL4, %s, hR4, hM4⟩ := hq4
'''%(', '.join(nv4),', '.join(h4))
# arithmetic
av=' '.join([A(k) if False else '(%s)'%A(k) for k in range(5)]+['(%s)'%U(j) for j in range(5)])
out+='''  have hQ := q_chain %s %s
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    %s
'''%(av,' '.join(qn),' '.join('h_'+n for n in qn))
# bounds for m limbs and others (readLE based, via h_ eqs)
def rb(v): return 'have b_%s : %s < 2 ^ 64 := by rw [h_%s]; exact Fv256.Util.readLE8_lt _ _'%(v,v,v)
for v in ['x114r1','x114r2','x114r5','x114m64','x114m72','x114m8','x114m16','x114m24','x114m32','x114m120']:
    out+='  '+rb(v)+'\n'
def mb(v): return 'have b_%s : %s < 2 ^ 64 := by rw [h_%s]; exact Nat.mod_lt _ (by decide)'%(v,v,v)
for v in nv2+nv3+nv4:
    if v in ('x2b4r8',): continue
    out+='  have b_%s : %s < 2 ^ 64 := by rw [h_%s]; exact Nat.mod_lt _ (by decide)\n'%(v,v,v) if v not in ('x284r26','x2f4r3','x2f4r4','x2f4r5','x2f4r6','x2f4r7') else ''
out+='''  have b_x284r26 : x284r26 < 2 ^ 64 := by rw [h_x284r26]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r3 : x1d8r3 < 2 ^ 64 := by rw [h_x1d8r3]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r4 : x1d8r4 < 2 ^ 64 := by rw [h_x1d8r4]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r6 : x1d8r6 < 2 ^ 64 := by rw [h_x1d8r6]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r7 : x1d8r7 < 2 ^ 64 := by rw [h_x1d8r7]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r9 : x1d8r9 < 2 ^ 64 := by rw [h_x1d8r9]; exact Nat.mod_lt _ (by decide)
  have hQM := qm_low x114r1 x114r2 x1d8r3 x1d8r4 x114r5 x1d8r6 x1d8r7 x1d8r9 x114m64 x284r3 x284r4 x284r5 x284r6 x284r26
    b_x114r1 b_x114r2 b_x1d8r3 b_x1d8r4 b_x114r5 b_x1d8r6 b_x1d8r7 b_x1d8r9 b_x114m64 h_x284r3 h_x284r4 h_x284r5 h_x284r6 h_x284r26
  have hSUB := r4_sub x284r26 x284r3 x284r4 x284r6 x284r5 x114m32 x114m24 x114m16 x114m120 x114m8 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8
    b_x284r26 b_x284r3 b_x284r4 b_x284r6 b_x284r5 b_x114m32 b_x114m24 b_x114m16 b_x114m120 b_x114m8 h_x2b4r3 h_x2b4r4 h_x2b4r5 h_x2b4r6 h_x2b4r7 h_x2b4r8
'''
out+="""
  have hF0 : x2b4r8 = 0 → x2f4r7 + 2 ^ 64 * x2f4r3 + 2 ^ 128 * x2f4r4 + 2 ^ 192 * x2f4r6 + 2 ^ 256 * x2f4r5 =
      x2b4r7 + 2 ^ 64 * x2b4r3 + 2 ^ 128 * x2b4r4 + 2 ^ 192 * x2b4r6 + 2 ^ 256 * x2b4r5 := fun h =>
    r4_fix0 x114r1 x114r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x114m64 x114m72 x2f4r3 x2f4r4 x2f4r5 x2f4r6 x2f4r7 h
      h_x2f4r3 h_x2f4r4 h_x2f4r5 h_x2f4r6 h_x2f4r7
  have hF1 : x2b4r8 ≠ 0 → x2f4r7 + 2 ^ 64 * x2f4r3 + 2 ^ 128 * x2f4r4 + 2 ^ 192 * x2f4r6 + 2 ^ 256 * x2f4r5 =
      ((x2b4r7 + 2 ^ 64 * x2b4r3 + 2 ^ 128 * x2b4r4 + 2 ^ 192 * x2b4r6 + 2 ^ 256 * x2b4r5) +
        (x114r2 + 2 ^ 64 * x114r1 + 2 ^ 128 * x114m64 + 2 ^ 192 * x114m72)) % 2 ^ 320 := fun h =>
    r4_fix1 x114r1 x114r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x114m64 x114m72 x2f4r3 x2f4r4 x2f4r5 x2f4r6 x2f4r7 h
      b_x114r1 b_x114r2 b_x2b4r3 b_x2b4r4 b_x2b4r5 b_x2b4r6 b_x2b4r7 b_x114m64 b_x114m72
      h_x2f4r3 h_x2f4r4 h_x2f4r5 h_x2f4r6 h_x2f4r7
  have e5 : x114r5 = x114m72 := by rw [h_x114r5, h_x114m72]
  rw [e5] at hQM
  rw [Fv256.Util.readLE_32, readLE_40] at hmu
  subst h_x114r1 h_x114r2 h_x114m64 h_x114m72 h_x114m8 h_x114m16 h_x114m24 h_x114m32 h_x114m120
  have hG := r4_glue (s.mem.readLE (BitVec.toNat (s.regs 1)) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 2)) 8) (s.mem.readLE (BitVec.toNat (s.regs 2) + 8) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 2) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 2) + 24) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 3)) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8)
    (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8)
    (x1d8r3 + 2 ^ 64 * x1d8r4 + 2 ^ 128 * x1d8r6 + 2 ^ 192 * x1d8r7 + 2 ^ 256 * x1d8r9)
    (x284r26 + 2 ^ 64 * x284r3 + 2 ^ 128 * x284r4 + 2 ^ 192 * x284r6 + 2 ^ 256 * x284r5)
    (x2f4r7 + 2 ^ 64 * x2f4r3 + 2 ^ 128 * x2f4r4 + 2 ^ 192 * x2f4r6 + 2 ^ 256 * x2f4r5)
    x2b4r8 (x2b4r7 + 2 ^ 64 * x2b4r3 + 2 ^ 128 * x2b4r4 + 2 ^ 192 * x2b4r6 + 2 ^ 256 * x2b4r5) _
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) hm3 hmu rfl hQ hQM hSUB.1 hSUB.2.1 hSUB.2.2 hF0 hF1
  obtain ⟨hG1, hG2⟩ := hG
  refine Fv256.Arm64.SegCompose.seg_mono (loop_run s hs (2 ^ 128) S4 _ _ _ _ _ _ _ _ _ hpc4 hR4 hM4 hL4 hG2) ?_
  intro S' h
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := h
  refine ⟨p1, p2, p3, p4, p5, p6, p7, ?_, p9⟩
  rw [p8, Fv256.Util.readLE_32 s.mem (s.regs 2).toNat, readLE_64 s.mem (s.regs 1).toNat]
  exact hG1

end Fv256.Arm64.R4Seg
"""
open('/srv/fv-uint256-wB3/lean/Fv256/Arm64/R4Sum.lean','w').write(out)
print(len(out))
