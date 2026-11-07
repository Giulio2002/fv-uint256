#!/usr/bin/env bash
set -e
cd /srv/fv-uint256-csa
f=lean/Fv256/Arm64/NewInt.lean
git checkout fv/wrun -- $f
sed -i '0,/^import Extracted/s//import Extracted\nimport Fv256.Arm64.CallSites.Base/' $f
sed -i 's/^namespace Fv256.Arm64.NewInt$/open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.NewInt/' $f
A='(Extracted.program.contractAddr "runtime.newobject")'
python3 scripts/callsite-splice.py $f nonvacuous --block lean/Fv256/Arm64/CallSites/NewInt.lean \
 --conj "∃ s_c : State, s_c.pc = BitVec.ofNat 64 $A ∧ NewobjectSite H rt 4096 s_c" --proof "⟨wsNew, rfl, wsNew_pre⟩"
