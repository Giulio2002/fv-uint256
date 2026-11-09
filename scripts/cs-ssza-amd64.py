#!/usr/bin/env python3
"""cs-ssza-amd64.py : MarshalSSZAppendMain amd64: growslice RtLive call site in both witnesses; the first witness' runtime serves the request."""
import subprocess
BLOCK = '''def csG0 : Amd64.State :=
  { s0 with regs := fun i => if i = 0 then dpV else if i = 3 then 40 else if i = 1 then 32 else if i = 7 then 8 else if i = 6 then BitVec.ofNat 64 u8A else if i = 4 then BitVec.ofNat 64 (sp0 - 64) else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `RSP = sp0 - 64`. -/
def csG : Amd64.State := { csG0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

theorem csG_rip : csG.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  have hw : argWords64 csG 5 = [dpA, 40, 32, 8, u8A] := by
    unfold argWords64 csG csG0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, hw, Contracts.arg]
    exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside, hw]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide)
  · show R.ok _ (argWords64 csG 5); rw [hw, addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)

'''
f = 'lean/Fv256/Proofs/Amd64/MarshalSSZAppendMain.lean'
s = open(f).read()
if 'import Fv256.Proofs.Amd64.CallSites.Live' not in s:
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
for a, b in [('def implAt : List Amd64.Segment := [growsliceSeg grA 0 16 8]\ndef ok : Nat → List Nat → Prop := fun _ _ => False',
              'def implAt : List Amd64.Segment := [growsliceSeg grA 32 64 64]\ndef ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]'),
             ('theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 1, 0, 1, (u8A, 1, 0).1] := fun _ h => h.elim',
              'theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2'),
             ('janus64_live_growslice (u8A, 1, 0) 1 0 1 16 8 hok_gr', 'janus64_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr')]:
    if a in s: s = s.replace(a, b, 1)
open(f, 'w').write(s)
bf = '/tmp/cs-ssza.lean'
open(bf, 'w').write(BLOCK)
A = '(Extracted.program.contractAddr "runtime.growslice")'
conj = f'∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 {A} ∧ RtLivePre64 4096 R growsliceSpec growsliceLive {A} [] 0x1000 s_c'
for nth, name in ((0, 'w1'), (1, 'w2')):
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf, '--block-name', name, '--nth', str(nth),
        '--conj', conj, '--proof', '⟨csG, csG_rip, csG_pre⟩'], capture_output=True, text=True)
    print(name, r.stdout.strip(), r.stderr.strip()[-300:])
