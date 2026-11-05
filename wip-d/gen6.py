root='/srv/fv-uint256-wd/lean/Fv256/'
t=open(root+'Arm64/SRsh.lean').read().split('\n')
i0=next(k for k,l in enumerate(t) if l.startswith('  rcases hzx with rfl | hzx'))
i1=next(k for k,l in enumerate(t) if k>i0+1 and l.startswith('  · simp only [Disjoint] at *'))
body=t[i0+1:i1]
while body and body[-1].strip()=='': body.pop()
body=[l[2:] if l.startswith('  ') else l for l in body]
body='\n'.join(body).replace('· simp only [Disjoint] at *','  simp only [Disjoint] at *',1)
out='''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).ISRsh(n uint) *Int` (arm64): in place arithmetic shift right, `z = z >> n` (sign-propagating)

**Guarantee.** For every pointer `z` (receiver, `X0`) and shift count `n` (`X1`, any 64-bit value), every Go call whose
stack-growth check falls through (`GuardOK s 56`: covers the check of `ISRsh` and of the `SRsh` it calls) and whose stack window
`[SP-112, SP)` (the frames of `ISRsh` and `SRsh`) is writable and aligned (`StackOK s 112 0`): if the 32 bytes at `z` are writable and
do not overlap the stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z`
afterwards is `Fv256.Spec.srsh` of the number at `z` before the call (the two's-complement reading shifted right by `n` with sign
fill; counts of 256 or more give 0 or all ones), and no byte changes outside `z[0..32)` and the stack window
(`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISRsh

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (z n : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s)
    (hg : GuardOK s 56) (hst : StackOK s 112 0) :
    (Ptr32 s.mem z true → Disjoint z.toNat 32 (s.sp.toNat - 112) 112 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.srsh (val256 s.mem z.toNat) n.toNat ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 112) 112)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  intro ⟨hz, hz'⟩ hd1
BODY

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem hg : GuardOK s0 56 := by unfold GuardOK; decide
theorem hst : StackOK s0 112 0 := by unfold StackOK; decide

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Disjoint z.toNat 32 (s0.sp.toNat - 112) 112 :=
  ⟨⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧ GuardOK s 56 ∧ StackOK s 112 0 ∧
    (Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 112) 112) :=
  ⟨ret, s0, z, n, hret, setup, hg, hst, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z n ret hret s0 setup hg hst hpre.1 hpre.2).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.ISRsh
'''.replace('BODY',body)
open(root+'Arm64/ISRsh.lean','w').write(out)
