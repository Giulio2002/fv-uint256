import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetAllOne() *Int` (arm64): `z = Fv256.Spec.allOne`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the 32 bytes at `z` are
writable, those at `x` readable (below `2^48`) and `z`, `x` are equal or disjoint, the call returns (no fault, no panic),
obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.allOne` of the number at `x` before the call,
and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `Spec.allOne`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetAllOne

theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z true)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.allOne ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨hz, hz'⟩
  janus_intro hs
  all_goals first | (exfalso; omega) | (janus_run; all_goals (simp [Spec.allOne, Spec.W]))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem z true :=
  ⟨by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (Ptr32 s.mem z true) :=
  ⟨ret, s0, z, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = Spec.allOne := by
  refine (correctness z ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  try decide

end Witness

end Fv256.Arm64.SetAllOne

