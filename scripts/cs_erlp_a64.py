#!/usr/bin/env python3
"""EncodeRLP arm64: newobject (NewobjectSite) + ICall (Write method, ICallPre) call sites."""
import subprocess
BLOCK = '''def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `X0 = Big`'s type descriptor, `SP = sp0 - 64` (the argument of `H` in `hH`). -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 64), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite H rt 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = tyA := by decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 64 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH tyA (Or.inl rfl)

/-- The call state of the `Write` method (U-WITNESS-CALLSITE): `Write(p)` with `p = (heap, 4, 4)` holding `rlpBytes (*z)` (the bytes `83 01 12 34` written at `heap`),
`X0 = w`, `SP = sp0 - 64`, at the method's entry. -/
def wsWr00 : State := { s0 with mem := s0.mem.writeLE heap 4 0x34120183 }
def wsWr0 : State := { wsWr00 with regs := fun i => if i = 0 then wA else if i = 1 then BitVec.ofNat 64 heap else if i = 2 then 4 else if i = 3 then 4 else s0.regs i }
def wsWr : State := { wsWr0 with sp := BitVec.ofNat 64 (sp0 - 64), pc := BitVec.ofNat 64 A0 }

set_option maxRecDepth 100000 in
theorem wsWr_pre : ICallPre 4 stack 96 rt
    (fun sc => sc.regs 0 = wA ∧
      StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem zA.toNat)) ∧
      (sc.regs 3).toNat = (sc.regs 2).toNat) wsWr := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide, ?_, rfl, ?_, by decide⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · refine ⟨by decide, by decide, fun _ => by decide, by decide⟩
'''
f = 'lean/Fv256/Arm64/EncodeRLP.lean'
subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
s = open(f).read()
s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
ns = 'namespace Fv256.Arm64.EncodeRLP\n'
s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
open(f, 'w').write(s)
bf = 'lean/Fv256/Arm64/CallSites/EncodeRLP.lean'
open(bf, 'w').write(BLOCK)
pc = lambda a: f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {a} ∧ '
N = '(Extracted.program.contractAddr "runtime.newobject")'
r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
  '--conj', pc(N) + 'NewobjectSite H rt 4096 s_c', '--proof', '⟨wsNew, rfl, wsNew_pre⟩',
  '--conj', pc('fn') + 'ICallPre 4 stack 96 rt (fun sc => sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧ (sc.regs 3).toNat = (sc.regs 2).toNat) s_c',
  '--proof', '⟨wsWr, rfl, wsWr_pre⟩'], capture_output=True, text=True)
print(r.stdout.strip(), r.stderr.strip()[-300:])
