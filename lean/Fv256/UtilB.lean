import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB

/-! Helper lemmas for family B (division, modular arithmetic, iterative numerics). -/

namespace Fv256.B

theorem clz_cases (v : Nat) (h : v < 2 ^ 64) : v = 0 ∨ Janus.Arm64.clzNat 64 v < 64 := by
  by_cases hv : v = 0
  · exact Or.inl hv
  · refine Or.inr ?_
    have := Fv256.Util.clz_bl 64 v h
    have h2 : 0 < Fv256.Spec.bitLen v := by
      unfold Fv256.Spec.bitLen; rw [if_neg hv]; omega
    omega

end Fv256.B

namespace Fv256.B

theorem append_toNat (E F : BitVec 64) : (E ++ F).toNat = E.toNat * 2 ^ 64 + F.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt F.isLt, Nat.shiftLeft_eq]

theorem extract12_append (E F : BitVec 64) :
    (BitVec.extractLsb' 12 64 (E ++ F)).toNat = (E.toNat * 2 ^ 64 + F.toNat) / 2 ^ 12 % 2 ^ 64 := by
  have h := append_toNat E F
  simp [BitVec.extractLsb'_eq_extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, h]

theorem writeLE_same (m : Janus.Arm64.Memory) (a n v w : Nat) :
    (m.writeLE a n v).writeLE a n w = m.writeLE a n w := by
  cases m with
  | mk bytes regions =>
  simp only [Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.mk.injEq, and_true]
  funext x
  by_cases h : a ≤ x ∧ x < a + n <;> simp [h]

end Fv256.B
