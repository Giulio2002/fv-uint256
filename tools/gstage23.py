#!/usr/bin/env python3
import sys,re; sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
from gb3 import *
b=bnd
st2=theorem_stmt(D+'RecipArith2.lean','sum2')
st3=theorem_stmt(D+'RecipArith3.lean','sum3')
concl2=st2[st2.index('∃ x160rcx'):].strip()
concl3=st3[st3.index('∃ x43crdx'):].strip()
fix=lambda c:c.replace('L1f3 s S ',"L1f3 s S' ").replace('L43c s S ',"L43c s S' ").replace('RecRegs s S ','RecRegs s S\' ').replace('S.mem',"S'.mem")
concl2=fix(concl2); concl3=fix(concl3)
V14=' '.join('x14c'+n for n in 'rax rcx rdx rbx rsi rdi r8 r9 m208 m210 m218 m220'.split())
V1f=' '.join('x1f3'+n for n in 'rax rcx rsi rdi r8 r9 r10 mb0 m208 m210 m218 m220'.split())
o='''import Fv256.Proofs.Amd64.RecipArith2
import Fv256.Proofs.Amd64.RecipArith3
import Fv256.Proofs.Amd64.RecipStart
import Fv256.Proofs.Amd64.RecipG.C_14c_1f3
import Fv256.Proofs.Amd64.RecipG.C_1f3_43c

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage2 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x14c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (%(V14)s : Nat)
    (hL : L14c s S %(V14)s) (hst : Start14c s y3 %(V14)s) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1f3)) S (fun S' =>
      %(C2)s) := by
  refine Fv256.SegCompose.seg_mono (c_14c_1f3 (y3 := y3) s S hpc hs hR hM %(V14)s hL) ?%(U)s
  intro S1 hq1
  exact sum2 s y3 %(V14)s S1 hq1 hst %(B2)s

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x1f3)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (%(V1f)s : Nat)
    (hL : L1f3 s S %(V1f)s) (hmb : x1f3mb0 = x1f3rax) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x43c)) S (fun S' =>
      %(C3)s) := by
  refine Fv256.SegCompose.seg_mono (c_1f3_43c (y3 := y3) s S hpc hs hR hM %(V1f)s hL) ?%(U)s
  intro S1 hq1
  exact sum3 s y3 %(V1f)s S1 hq1 %(B3)s hmb

end Fv256.Amd64.RecipSeg
''' % dict(V14=V14,V1f=V1f,C2=concl2,C3=concl3,U='_',B2=b('L14c','x14cm218','hL'),
  B3=' '.join(b('L1f3',v,'hL') for v in ['x1f3rax','x1f3r10','x1f3rsi','x1f3rdi','x1f3r8','x1f3r9']))
open(D+'RecipStage23.lean','w').write(o)
