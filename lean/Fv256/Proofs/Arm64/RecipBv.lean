import Janus
import Fv256.Proofs.Common.UtilB

/-! BitVec normalisation lemmas for the arm64 `Reciprocal` stage proofs -/
set_option linter.unusedSimpArgs false

namespace Fv256.Arm64.RecipBv

theorem rot32_shl (x : BitVec 64) :
    x.rotateRight 32 &&& 18446744069414584320#64 &&& 18446744073709551615#64 = x <<< 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have t1 : ∀ i, i < 64 → Nat.testBit 18446744069414584320 i = decide (32 ≤ i) := by decide
  have t2 : ∀ i, i < 64 → Nat.testBit 18446744073709551615 i = true := by decide
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, t1 i hi, t2 i hi]
  by_cases h : i < 32
  · simp [h, hi]
  · have h2 : ¬ i < 64 - 32 % 64 := by omega
    simp [h, h2, hi]
    intro _; omega

theorem rot32_hi (x : BitVec 64) :
    (x.rotateRight 32).toNat &&& 18446744069414584320 = x.toNat * 2 ^ 32 % 2 ^ 64 := by
  have h := congrArg BitVec.toNat (rot32_shl x)
  simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft] at h
  have e : (18446744073709551615#64).toNat = 18446744073709551615 := rfl
  have e2 : (18446744069414584320#64).toNat = 18446744069414584320 := rfl
  rw [e, e2] at h
  have hlt : (x.rotateRight 32).toNat &&& 18446744069414584320 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  rw [Nat.and_assoc] at h
  have e3 : 18446744069414584320 &&& 18446744073709551615 = 18446744069414584320 := by decide
  rw [e3] at h
  simpa [Nat.shiftLeft_eq] using h

theorem toNat_ite (c : Prop) [Decidable c] (a b : BitVec 64) :
    (if c then a else b).toNat = if c then a.toNat else b.toNat := by split <;> rfl

end Fv256.Arm64.RecipBv
