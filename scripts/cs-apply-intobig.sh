#!/usr/bin/env bash
# re-apply the IntoBig arm64 call-site block from CallSites/IntoBig.lean onto a pristine witness file
set -e
cd /srv/fv-uint256-csa
f=lean/Fv256/Arm64/IntoBig.lean
git checkout fv/wrun -- $f
sed -i '1i import Fv256.Arm64.CallSites.Base' $f
sed -i 's/^namespace Fv256.Arm64.IntoBig$/open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.IntoBig/' $f
python3 - <<'PY'
import subprocess
A='(Extracted.program.contractAddr "%s")'
nw=A%'runtime.newobject'
nw=A%'runtime.newobject'
new='∃ (s_c : State), s_c.pc = BitVec.ofNat 64 %s ∧ NewobjectLiveSite R %s 4096 [] 0x400 s_c'%(nw,nw)
def wb(n):
    a=A%('runtime.gcWriteBarrier%d'%n)
    return '∃ (s_c : State), s_c.pc = BitVec.ofNat 64 %s ∧ WbLiveSite R %s 4096 %d [] 0x400 s_c'%(a,a,n)
args=['python3','scripts/callsite-splice.py','lean/Fv256/Arm64/IntoBig.lean','nonvacuous','--block','lean/Fv256/Arm64/CallSites/IntoBig.lean']
for c,p in ((new,'⟨csNew, rfl, csNew_pre⟩'),(wb(1),'⟨csW1, rfl, csW1_pre⟩'),(wb(2),'⟨csW2, rfl, csW2_pre⟩')):
    args+=['--conj',c,'--proof',p]
print(subprocess.run(args,capture_output=True,text=True).stdout)
PY
