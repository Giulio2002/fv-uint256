import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).ExtendSign(x, byteNum *Int) *Int` (arm64): sign extension from byte `byteNum`

**Guarantee.** For all pointers `z` (receiver, `X0`), `x` (`X1`) and `y = byteNum` (`X2`) and every Go call state with the 32 bytes at `z`
writable and those at `x`, `y` readable (below `2^48`), where every pair of the three pointers is equal or disjoint, the call returns
(no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.extendSign` of the numbers at `x`
(the value) and `y` (the byte index, a full 256-bit number: indices of 31 or more leave `x` unchanged) before the call, and no byte
outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ExtendSign

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.extendSign (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  · rcases hzy with rfl | hzy
    · @@A@@
    · @@B@@
  · rcases hzy with rfl | hzy
    · @@C@@
    · rcases hxy with rfl | hxy
      · @@D@@
      · @@E@@

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Aliasing z x ∧ Aliasing z x ∧ Aliasing x x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inl rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
      Aliasing z x ∧ Aliasing z y ∧ Aliasing x y) :=
  ⟨ret, s0, z, x, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.ExtendSign
