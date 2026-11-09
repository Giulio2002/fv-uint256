import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Not(x *Int) *Int` (arm64): `z = Fv256.Spec.not x`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the 32 bytes at `z` are
writable, those at `x` readable (below `2^48`) and `z`, `x` are equal or disjoint, the call returns (no fault, no panic),
obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.not` of the number at `x` before the call,
and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `Spec.not 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Not

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.not (val256 s.mem x.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat )); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24)); simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Spec.not, Spec.W]; omega))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.not (val256 s.mem x.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = Spec.not 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.Not
