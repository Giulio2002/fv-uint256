#!/usr/bin/env python3
"""MarshalSSZAppendMain arm64: growslice RtLive call site in both witnesses (Witness, Grow.Witness). The first witness' runtime is changed to
serve the request (ok = Grow's ok, same stub) so that a call-site state exists."""
import subprocess
BLOCK = '''def csG0 : State := { s0 with regs := fun i => if i = 0 then dpV else if i = 1 then 40 else if i = 2 then 32 else if i = 3 then 8 else if i = 4 then BitVec.ofNat 64 u8A else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `SP = sp0 - 128`. -/
def csG : State := { csG0 with sp := BitVec.ofNat 64 (sp0 - 128), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, argWords, wordsFrom, arg]
    exact ⟨⟨typeOK_of (by decide) (by decide), by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [argWords, wordsFrom, arg, Outside, calleeStack]; decide)
  · rw [addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)
'''
f = 'lean/Fv256/Arm64/MarshalSSZAppendMain.lean'
subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
s = open(f).read()
s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
ns = 'namespace Fv256.Arm64.MarshalSSZAppendMain\n'
s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
# first witness: serve the request
a = '''def implAt : List Segment := [growsliceSeg grA 0 16 8]
def ok : Nat → List Nat → Prop := fun _ _ => False'''
b = '''def implAt : List Segment := [growsliceSeg grA 32 64 64]
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]'''
assert a in s; s = s.replace(a, b, 1)
a = 'theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 1, 0, 1, (u8A, 1, 0).1] := fun _ h => h.elim'
b = 'theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2'
assert a in s; s = s.replace(a, b, 1)
a = 'janus_live_growslice (u8A, 1, 0) 1 0 1 16 8 hok_gr'
b = 'janus_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr'
assert a in s; s = s.replace(a, b, 1)
s = s.replace('so no `growslice` request is made\n(the runtime serves none: `ok` is false) and the contract holds vacuously at the generic stub runtime.',
              'so no `growslice` request is made by the code;\nthe stub runtime serves the request `growslice(p, 40, 32, 8, uint8)` (as in `Grow.Witness`) so that the call-site state exists.', 1)
open(f, 'w').write(s)
bf = 'lean/Fv256/Arm64/CallSites/MarshalSSZAppendMain.lean'
open(bf, 'w').write(BLOCK)
A = '(Extracted.program.contractAddr "runtime.growslice")'
conj = f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {A} ∧ RtLivePre 4096 R growsliceSpec growsliceLive {A} [] 0x1000 s_c'
for nth, name in ((0, 'w1'), (1, 'w2')):
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf, '--block-name', name, '--nth', str(nth),
        '--conj', conj, '--proof', '⟨csG, rfl, csG_pre⟩'], capture_output=True, text=True)
    print(name, r.stdout.strip(), r.stderr.strip()[-300:])
