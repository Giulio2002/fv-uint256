#!/usr/bin/env bash
# re-apply the IntoBig arm64 call-site block from CallSites/IntoBig.lean onto a pristine witness file
set -e
cd /srv/fv-uint256-csa
f=lean/Fv256/Arm64/IntoBig.lean
git checkout $f
sed -i '1i import Fv256.Arm64.CallSites.Base' $f
sed -i 's/^namespace Fv256.Arm64.IntoBig$/open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.IntoBig/' $f
python3 - <<'PY'
import subprocess
A='(Extracted.program.contractAddr "%s")'
nw=A%'runtime.newobject'
new='∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 %s ∧ NewobjectPre 4096 s_c ∧ StackRoom s_c 4096 1 ∧ LiveAt R %s [(s_c.regs 0).toNat] L b (newobjectRound s_c) (s_c.regs 28).toNat s_c.mem (calleeStack s_c 4096 1)'%(nw,nw)
def wb(n):
    a=A%('runtime.gcWriteBarrier%d'%n)
    return '∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.pc = BitVec.ofNat 64 %s ∧ CallOK s_c 4096 0 ∧ R.ok %s [%d] ∧ R.inv b L (s_c.regs 28).toNat (view R.rt L s_c.mem) ∧ LiveSep L [(s_c.sp.toNat - 4096, s_c.sp.toNat - 8)] ∧ LiveSep [(s_c.sp.toNat - 4096, s_c.sp.toNat - 8)] R.rt'%(a,a,n)
args=['python3','scripts/callsite-splice.py','lean/Fv256/Arm64/IntoBig.lean','nonvacuous','--block','lean/Fv256/Arm64/CallSites/IntoBig.lean']
for c,p in ((new,'⟨[], 0x400, csNew, rfl, csNew_pre⟩'),(wb(1),'⟨[], 0x400, csW1, rfl, csW1_pre⟩'),(wb(2),'⟨[], 0x400, csW2, rfl, csW2_pre⟩')):
    args+=['--conj',c,'--proof',p]
print(subprocess.run(args,capture_output=True,text=True).stdout)
PY
