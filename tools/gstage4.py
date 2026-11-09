#!/usr/bin/env python3
import sys; sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
from gb3 import *
p4vars,l660,facts,mp,hh,q660=gen_stage4()
R='(x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx)'
sm={'x502rcx':'x43crcx','x502rsi':'y3','x502m98':'x43cr8','x502ma0':'x43crbx','x502ma8':'x43crdx','x502m208':'x43cm208','x502m210':'x43cm210','x502m218':'x43cm218','x502m220':'y3'}
l660s=[sm.get(v,v) for v in l660]
facts_s=[subst(f,sm) for f in facts]
wn={'0':'(sqw %s 0)'%R,'1':'x502r10','2':'x502rdi','3':'x502r8','4':'x502rbx','5':'x502r9'}
yn={'0':'x43cm208','1':'x43cm210','2':'x43cm218','3':'y3'}
b=bnd
fn=['f%d'%i for i in range(len(facts))]
L=[]
w=L.append
w('''import Fv256.Proofs.Amd64.RecipArith4
import Fv256.Proofs.Amd64.RecipArith4p
import Fv256.Proofs.Amd64.RecipArith4q
import Fv256.Proofs.Amd64.RecipArith4s
import Fv256.Proofs.Amd64.RecipStage5Lem
import Fv256.Proofs.Amd64.RecipG.C_43c_502
import Fv256.Proofs.Amd64.RecipG.C_502_660
import Fv256.Proofs.Amd64.RecipG.C_660_7ae
import Fv256.Proofs.Amd64.RecipG.G_7ae_801

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

/-- the seven-word sum of stage 4 in terms of the squaring words `w_i` and `y_j` -/
def stage4T (w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 : Nat) : Nat :=
  2 ^ 0 * (w0 * y3 + w1 * y2 + w2 * y1 + w3 * y0) + 2 ^ 64 * (w1 * y3 + w2 * y2 + w3 * y1 + w4 * y0) + 2 ^ 128 * (w2 * y3 + w3 * y2 + w4 * y1 + w5 * y0) + 2 ^ 192 * (w3 * y3 + w4 * y2 + w5 * y1) + 2 ^ 256 * (w4 * y3 + w5 * y2) + 2 ^ 320 * (w5 * y3)

/-- the machine value of `r4pre` (`recipR4pre`) from `r3` and the words of `y` -/
def r4preF (r3 y0 y1 y2 y3 : Nat) : Nat :=
  (r3 * 2 ^ 256 + 2 ^ 448 - stage4T (sqw r3 0) (sqw r3 1) (sqw r3 2) (sqw r3 3) (sqw r3 4) (sqw r3 5) y0 y1 y2 y3) % 2 ^ 448 / 2 ^ 128
''')
w('set_option maxHeartbeats 64000000 in\nset_option maxRecDepth 200000 in')
w('''theorem stage4 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x43c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x43crcx x43crdx x43crbx x43cr8 x43cm208 x43cm210 x43cm218 : Nat)
    (hL : L43c s S x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x801)) S (fun S' =>
      ∃ x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60,
        L801 s S' x43crcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x43cm208 x43cm210 x43cm218 y3 ∧
        x801rdx + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40 =
          r4preF %s x43cm208 x43cm210 x43cm218 y3 ∧
        x801rdx = x801m60 ∧ x801r8 = x801m50 ∧ x801r9 = x801m48 ∧ x801rsi = x801m40 ∧
        RecRegs s S' ∧ RecMem s S'.mem y3) := by''' % R)
w('  refine Fv256.SegCompose.seg_trans (c_43c_502 (y3 := y3) s S hpc hs hR hM x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL) ?_')
w('  intro S1 hpc1 hq1')
w('  have hA := sum4a s y3 x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 S1 hq1 %s %s %s %s' % (b('L43c','x43crdx','hL'),b('L43c','x43crbx','hL'),b('L43c','x43cr8','hL'),b('L43c','x43crsi','hL')))
w('  obtain ⟨x502rbx, x502rdi, x502r8, x502r9, x502r10, x502m68, x502m70, hL1, hR1, hM1, e1, e2, e3, e4, e5, e0⟩ := hA')
w('  refine Fv256.SegCompose.seg_trans (c_502_660 (y3 := y3) s S1 hpc1 hs hR1 hM1 x43crcx x502rbx y3 x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL1) ?_')
w('  intro S2 hpc2 hq2')
bs=[b('L502',v,'hL1') for v in ['x502r10','x502rdi','x502r8','x502rbx','x502r9','x502m70','x502m68','x502m208','x502m210','x502m218','x502m220']]
w('  have hP := sum4p s y3 x43crcx x502rbx y3 x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 S2 hq2 %s rfl' % ' '.join(bs))
w('  obtain ⟨%s, hL2, hR2, hM2, %s⟩ := hP' % (', '.join(p4vars), ', '.join(fn)))
w('  refine Fv256.SegCompose.seg_trans (c_660_7ae (y3 := y3) s S2 hpc2 hs hR2 hM2 %s hL2) ?_' % ' '.join(l660s))
w('  intro S3 hpc3 hq3')
# hl/hh
fact_by_lo={}
for f,nm in zip(facts_s,fn):
    lo=f.split(' + ')[0]; fact_by_lo[lo]=nm
fact_by_lo['x502m70']='e0'
hyps=[]
for kind,ij,qv,wi,yj,op in hh:
    act=sm.get(mp[qv],mp[qv])
    # lo var of the pair: for hl it's act; for hh find the pair whose hi is act
    hyps.append((kind,ij,qv,act))
# build pairs
pairs={}
for kind,ij,qv,act in hyps:
    pairs.setdefault(ij,{})[kind]=(qv,act)
lines=[]
hnames=[]
for ij,d in pairs.items():
    qlo,alo=d['hl']; 
    f=fact_by_lo[alo]
    lines.append('  have hlh%s := lohi _ _ _ %s %s' % (ij,b('L660',qlo,'hL2'),f))
    hnames += ['hlh%s.1'%ij,'hlh%s.2'%ij]
# order of hypotheses as in sum4q signature: hl12 hh12 hl13 hh13 ...
order=[(k+ij) for (k,ij,_,_,_,_) in hh]
args=[]
for k,ij,_,_,_,_ in hh:
    args.append('hlh%s.%d'%(ij,1 if k=='hl' else 2))
for l in lines: w(l)
by0=[b('L502',v,'hL1') for v in ['x502r10','x502rdi','x502r8','x502rbx','x502r9']]
bw0='(Nat.mod_lt _ (by decide))'
bys=[b('L502',v,'hL1') for v in ['x502m208','x502m210','x502m218','x502m220']]
w('  have hQ := sum4q s y3 %s %s %s x502r10 x502rdi x502r8 x502rbx x502r9 x43cm208 x43cm210 x43cm218 y3 S3 hq3 %s %s %s' % (' '.join(l660s), '', wn['0'], bw0, ' '.join(by0), ' '.join(bys)) + ' ' + ' '.join(args))
w('  obtain ⟨x7aerax, x7aerdx, x7aerbx, x7aersi, x7aerdi, x7aer8, x7aer11, hL3, hR3, hM3, hT⟩ := hQ')
w('  refine Fv256.SegCompose.seg_mono (g_7ae_801 (y3 := y3) s S3 hpc3 hs hR3 hM3 x7aerax x43crcx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL3) ?_')
w('  intro S4 hq4')
w('  unfold P_7ae_801 at hq4')
w('  obtain ⟨x801rdx, x801rbx, x801rsi, x801r8, x801r9, x801m40, x801m48, x801m50, x801m60, hL4, h_x801rdx, h_x801rbx, h_x801rsi, h_x801r8, h_x801r9, h_x801m40, h_x801m48, h_x801m50, h_x801m60, hR4, hM4⟩ := hq4')
sb=[b('L7ae',v,'hL3') for v in ['x7aerax','x7aerdx','x7aerbx','x7aersi','x7aerdi','x7aer8','x7aer11','x7aem98','x7aema0','x7aema8']]
w('  have hsb := sbb4 x7aerax x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x43cr8 x43crbx x43crdx x801rdx x801rbx x801m50 x801m48 x801m40 %s h_x801rdx h_x801rbx h_x801m40 h_x801m48 h_x801m50' % ' '.join(sb))
w('  refine ⟨x801rdx, x801rbx, x801rsi, x801r8, x801r9, x801m40, x801m48, x801m50, x801m60, hL4, ?_, h_x801rdx.trans h_x801m60.symm, h_x801r8.trans h_x801m50.symm, h_x801r9.trans h_x801m48.symm, h_x801rsi.trans h_x801m40.symm, hR4, hM4⟩')
w('  rw [hsb, hT]')
w('  subst e1 e2 e3 e4 e5')
w('  rfl')
w('\nend Fv256.Amd64.RecipSeg')
open('/srv/fv-uint256-wBm/lean/Fv256/Proofs/Amd64/RecipStage4.lean','w').write('\n'.join(L)+'\n')
