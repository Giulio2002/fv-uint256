#!/usr/bin/env python3
"""MarshalSSZ (len 0, cap 32) and PaddedBytes (n = cap = 5) arm64: runtime.makeslice call-site (MakesliceSite)."""
import subprocess, sys
CFG = {'MarshalSSZ': (0, 32), 'PaddedBytes': (5, 5)}
BLOCK = '''def csMk0 : State := {{ s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 1 then {L}#64 else if i = 2 then {C}#64 else s0.regs i }}
/-- The call state of `runtime.makeslice` (U-WITNESS-CALLSITE): `makeslice(uint8, {L}, {C})` at its entry in the caller's frame (`SP = sp0 - 48`, as in `hH`). -/
def csMk : State := {{ csMk0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") }}

set_option maxRecDepth 100000 in
theorem csMk_pre : MakesliceSite H rt 4096 csMk := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide, by decide, by decide⟩, ?_⟩
  have e0 : (csMk.regs 0).toNat = byteType := by
    have hpt : byteType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (csMk.regs 1).toNat = {L} := by decide
  have e2 : (csMk.regs 2).toNat = {C} := by decide
  have e3 : (csMk.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e4 : csMk.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(csMk.regs 0).toNat, (csMk.regs 1).toNat, (csMk.regs 2).toNat] (csMk.regs 28).toNat csMk.sp.toNat (rtView rt csMk.mem)
  rw [e0, e1, e2, e3, e4]
  exact hH
'''
for fn in sys.argv[1:]:
    L, C = CFG[fn]
    f = f'lean/Fv256/Arm64/{fn}.lean'
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
    s = open(f).read()
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    ns = f'namespace Fv256.Arm64.{fn}\n'
    s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
    open(f, 'w').write(s)
    bf = f'lean/Fv256/Arm64/CallSites/{fn}.lean'
    open(bf, 'w').write(BLOCK.format(L=L, C=C))
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
        '--conj', '∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ MakesliceSite H rt 4096 s_c',
        '--proof', '⟨csMk, rfl, csMk_pre⟩'], capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-200:])
