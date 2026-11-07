import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Mul(x, y) *Int` (arm64): `z = x * y`

**Guarantee.** For all pointers `z`, `x`, `y` and every Go call state with them in `X0` (receiver), `X1`, `X2` such that
the 32 bytes at `z` are writable and those at `x`, `y` readable (below `2^48`), and every pair of the three pointers is
equal or disjoint, the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Mul

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy <;> rcases hxy with h | hxy
  all_goals try subst h
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try have := Util.readLE8_lt s.mem (y.toNat )); (try have := Util.readLE8_lt s.mem (y.toNat + 8)); (try have := Util.readLE8_lt s.mem (y.toNat + 16)); (try have := Util.readLE8_lt s.mem (y.toNat + 24)); simp only [Spec.mul, Spec.W, Nat.reducePow]; janus_arith))

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
      Aliasing z x ∧ Aliasing z y ∧ Aliasing x y) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.Mul
