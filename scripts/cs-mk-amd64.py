#!/usr/bin/env python3
"""cs-mk-amd64.py FN... : MarshalSSZ (len 0, cap 32) and PaddedBytes (n = cap = 5) amd64: runtime.makeslice call-site (MakesliceSite)."""
import subprocess, sys
CFG = {'MarshalSSZ': (0, 32), 'PaddedBytes': (5, 5)}
BLOCK = '''/-- The call state of `runtime.makeslice` (U-WITNESS-CALLSITE): `makeslice(uint8, {L}, {C})` at its entry in the caller's frame (`RSP = sp0 - 40`, as in `hH`). -/
def csMk : Janus.Amd64.State :=
  {{ s0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice"),
    regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 3 then {L}#64 else if i = 1 then {C}#64 else if i = 4 then BitVec.ofNat 64 (sp0 - 40) else s0.regs i }}

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csMk_pre : MakesliceSite H rt 4096 csMk := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  have e0 : (csMk.regs 0).toNat = byteType := by
    have hpt : byteType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (csMk.regs 3).toNat = {L} := by decide
  have e2 : (csMk.regs 1).toNat = {C} := by decide
  have e3 : (csMk.regs 14).toNat = (s0.regs 14).toNat := by decide
  have e4 : (csMk.regs 4).toNat = (s0.regs 4).toNat - 40 := by decide
  show H [(csMk.regs 0).toNat, (csMk.regs 3).toNat, (csMk.regs 1).toNat] (csMk.regs 14).toNat (csMk.regs 4).toNat (rtView rt csMk.mem)
  rw [e0, e1, e2, e3, e4]
  exact hH

'''
for fn in sys.argv[1:]:
    L, C = CFG[fn]
    f = f'lean/Fv256/Amd64/{fn}.lean'
    s = open(f).read()
    if 'import Fv256.Amd64.CallSites.Live' not in s:
        s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
    open(f, 'w').write(s)
    bf = f'/tmp/cs-{fn}-mk.lean'
    open(bf, 'w').write(BLOCK.format(L=L, C=C))
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf, '--block-name', fn + '.mk',
        '--conj', '∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ Fv256.CallSites.MakesliceSite H rt 4096 s_c',
        '--proof', '⟨csMk, rfl, csMk_pre⟩'], capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-200:])
