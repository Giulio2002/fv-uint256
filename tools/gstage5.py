#!/usr/bin/env python3
import sys,re; sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
from gb3 import *
b=bnd
st=theorem_stmt(D+'RecipArith5p.lean','sum5p')
m=re.search(r'∃ ([^,]*), (L9d4 s S [^∧]*)∧ RecRegs s S ∧ RecMem s S.mem y3 ∧(.*)$',st,re.S)
p5vars=m.group(1).split(); l9=m.group(2).split()[3:]; facts=split_conj(m.group(3).strip())
q9,_=ldef('L9d4'); mp=dict(zip(q9,l9))
qst=theorem_stmt(D+'RecipArith5q.lean','sum5q')
hh=re.findall(r'\((h[lh])(\d\d) : (\S+) = w(\d) \* y(\d) (%|/) 18446744073709551616\)',qst)
m2=re.search(r'∃ ([^,]*), Lb47 s S ([^∧]*)∧',qst)
q5vars=m2.group(1).split(); lb47=[mp.get(v,v) for v in m2.group(2).split()]
fn=['f%d'%i for i in range(len(facts))]
W={'0':'x801m60','1':'x801rbx','2':'x801m50','3':'x801m48','4':'x801m40'}
Y={'0':'x801m208','1':'x801m210','2':'x801m218','3':'y3'}
R4p='(x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40)'
YY='(x801m208 + 2 ^ 64 * x801m210 + 2 ^ 128 * x801m218 + 2 ^ 192 * y3)'
Wd='(if 2 ^ 574 < %s * %s then (%s + 2 ^ 320 - 1) %% 2 ^ 320 else %s)'%(R4p,YY,R4p,R4p)
V14='x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 y3'
L=[]; w=L.append
w('''import Fv256.Amd64.RecipArith5p
import Fv256.Amd64.RecipArith5q
import Fv256.Amd64.RecipArith5c
import Fv256.Amd64.RecipArith5d
import Fv256.Amd64.RecipStage5Lem
import Fv256.Amd64.RecipG.C_801_9d4
import Fv256.Amd64.RecipG.C_9d4_b47
import Fv256.Amd64.RecipG.G_b47_b9f
import Fv256.Amd64.RecipG.G_b9f_bed
import Fv256.Amd64.RecipG.G_bed_c49

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage5 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x801)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 : Nat)
    (hL : L801 s S x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 y3)
    (e1 : x801rdx = x801m60) (e2 : x801r8 = x801m50) (e3 : x801r9 = x801m48) (e4 : x801rsi = x801m40) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xc49)) S (fun S' =>
      ∃ xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90,
        Lc49 s S' xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 ∧
        xc49rcx = (if 2 ^ 63 ≤ x801rcx then 0 else x801rcx) ∧
        xc49rdx + 2 ^ 64 * xc49rbx + 2 ^ 128 * xc49rsi + 2 ^ 192 * xc49r9 + 2 ^ 256 * xc49r11 =
          (if 2 ^ 63 ≤ x801rcx then 2 * %(Wd)s %% 2 ^ 320 else %(Wd)s) ∧
        xc49m78 = xc49rbx ∧ xc49m80 = xc49rsi ∧ xc49m88 = xc49r9 ∧ xc49m90 = xc49r11 ∧
        RecRegs s S' ∧ RecMem s S'.mem y3) := by''' % dict(Wd=Wd))
w('  refine Fv256.SegCompose.seg_trans (c_801_9d4 (y3 := y3) s S hpc hs hR hM %s hL) ?_' % V14)
w('  intro S1 hpc1 hq1')
bp=[b('L801',v,'hL') for v in ['x801m60','x801rbx','x801m50','x801m48','x801m40','x801m208','x801m210','x801m218','x801m220']]
w('  have hP := sum5p s y3 %s S1 hq1 %s e1 e2 e3 e4' % (V14,' '.join(bp)))
w('  obtain ⟨%s, hL1, hR1, hM1, %s⟩ := hP' % (', '.join(p5vars),', '.join(fn)))
w('  refine Fv256.SegCompose.seg_trans (c_9d4_b47 (y3 := y3) s S1 hpc1 hs hR1 hM1 %s hL1) ?_' % ' '.join(l9))
w('  intro S2 hpc2 hq2')
fact_by_lo={f.split(' + ')[0]:nm for f,nm in zip(facts,fn)}
pairs={}
for kind,ij,qv,wi,yj,op in hh:
    pairs.setdefault(ij,{})[kind]=(qv,mp[qv])
lines=[]
for ij,d in pairs.items():
    qlo,alo=d['hl']
    lines.append('  have hlh%s := lohi _ _ _ %s %s' % (ij,b('L9d4',qlo,'hL1'),fact_by_lo[alo]))
args=['hlh%s.%d'%(ij,1 if k=='hl' else 2) for k,ij,_,_,_,_ in hh]
for l in lines: w(l)
bw=[b('L801',v,'hL') for v in ['x801m60','x801rbx','x801m50','x801m48','x801m40','x801m208','x801m210','x801m218','x801m220']]
w('  have hQ := sum5q s y3 %s %s %s S2 hq2 %s %s' % (' '.join(l9),' '.join(W[str(i)] for i in range(5)),' '.join(Y[str(i)] for i in range(4)),' '.join(bw),' '.join(args)))
w('  obtain ⟨%s, hL2, hR2, hM2, hT⟩ := hQ' % ', '.join(q5vars))
w('  refine Fv256.SegCompose.seg_trans (g_b47_b9f (y3 := y3) s S2 hpc2 hs hR2 hM2 %s hL2) ?_' % ' '.join(lb47))
w('  intro S3 hpc3 hq3')
w('  obtain ⟨xb9frdx, hL3, hc, hR3, hM3⟩ := hq3')
# sum5c: m100 rsi r12 r10 r8 r15 rax rdx r13
names5c=['xb47m100','xb47rsi','xb47r12','xb47r10','xb47r8','xb47r15','xb47rax','xb47rdx','xb47r13']
act=dict(zip(['xb47rax','xb47rcx','xb47rdx','xb47rbx','xb47rsi','xb47r8','xb47r10','xb47r12','xb47r13','xb47r15','xb47m40','xb47m48','xb47m50','xb47m60','xb47m100'],lb47))
w('  have hc2 := sum5c %s xb9frdx %s hc' % (' '.join(act[v] for v in names5c),' '.join(b('Lb47',v,'hL2') for v in names5c)))
w('  refine Fv256.SegCompose.seg_trans (g_b9f_bed (y3 := y3) s S3 hpc3 hs hR3 hM3 x801rcx xb9frdx x801rbx x801m40 x801m48 x801m50 x801m60 hL3) ?_')
w('  intro S4 hpc4 hq4')
w('  obtain ⟨xbedrdi, xbedr8, xbedr10, xbedr12, xbedr15, hL4, hdi, hd8, hd10, hd12, hd15, hR4, hM4⟩ := hq4')
bd=[b('Lb9f',v,'hL3') for v in ['xb9fm60','xb9frbx','xb9fm50','xb9fm48','xb9fm40']]
w('  have hd := sum5d xb9frdx x801m60 x801rbx x801m50 x801m48 x801m40 xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 (by rw [hc2]; split <;> omega) %s hdi hd8 hd10 hd12 hd15' % ' '.join(bd))
w('  refine Fv256.SegCompose.seg_mono (g_bed_c49 (y3 := y3) s S4 hpc4 hs hR4 hM4 x801rcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 hL4) ?_')
w('  intro S5 hq5')
w('  unfold P_bed_c49 at hq5')
w('  obtain ⟨xc49rcx, xc49rdx, xc49rbx, xc49rsi, xc49r9, xc49r11, xc49m78, xc49m80, xc49m88, xc49m90, hL5, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, hR5, hM5⟩ := hq5')
w('  have hW : xbedrdi + 2 ^ 64 * xbedr8 + 2 ^ 128 * xbedr10 + 2 ^ 192 * xbedr12 + 2 ^ 256 * xbedr15 = %s := by' % Wd)
w('    rw [hT, stage5T_eq] at hc2')
w('    exact r4step _ _ _ _ _ (by omega) hd hc2 rfl')
ld=[b('Lbed',v,'hL4') for v in ['xbedrdi','xbedr8','xbedr10','xbedr12','xbedr15']]
w('  have bd0 := %s\n  have bd1 := %s\n  have bd2 := %s\n  have bd3 := %s\n  have bd4 := %s' % tuple(ld))
w('  have bcx := %s' % b('L801','x801rcx','hL'))
w("  have hW : xbedrdi + 2 ^ 64 * xbedr8 + 2 ^ 128 * xbedr10 + 2 ^ 192 * xbedr12 + 2 ^ 256 * xbedr15 = %s := by" % Wd)
w('    rw [hT, stage5T_eq] at hc2')
w('    exact r4step _ _ _ _ _ (by omega) hd hc2 rfl')
w('  have hdb := dbl5 x801rcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 bcx bd0 bd1 bd2 bd3 bd4 g1 g2 g3 g4 g5')
w('  rw [hW] at hdb')
M='18446744073709551616'
w('  refine ⟨xc49rcx, xc49rdx, xc49rbx, xc49rsi, xc49r9, xc49r11, xc49m78, xc49m80, xc49m88, xc49m90, hL5, rcx_dbl _ _ bcx g0, hdb, ?_, ?_, ?_, ?_, hR5, hM5⟩')
w('  · exact cpy _ _ _ _ _ bd1 g2 g6')
w('  · exact cpy _ _ _ _ _ bd2 g3 g7')
w('  · exact cpy _ _ _ _ _ bd3 g4 g8')
w('  · exact cpy _ _ _ _ _ bd4 g5 g9')
w('\nend Fv256.Amd64.RecipSeg')
open(D+'RecipStage5.lean','w').write('\n'.join(L)+'\n')
