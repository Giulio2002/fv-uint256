import Fv256.SpecI
import Fv256.UtilI

/-! Pure lemmas for the top level of `SetFromDecimal` (arm64): the branch-free `s[1:]` pointer mask, etc. -/

namespace Fv256.TopMath

theorem msb_neg (m : BitVec 64) (h0 : m ≠ 0#64) (h1 : m.toNat < 2 ^ 63) : (0#64 - m).getLsbD 63 = true := by
  have hm : 0 < m.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  have : (0#64 - m).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simpa [BitVec.msb_eq_getLsbD_last] using this

theorem asr_and1 (m : BitVec 64) (hm : m.toNat < 2 ^ 63) :
    (((if (0#64 - m).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 |||
        (0#64 - m).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) &&& 1#64) =
      if m = 0#64 then 0#64 else 1#64 := by
  by_cases h0 : m = 0#64
  · subst h0; decide
  · rw [if_neg h0, if_pos (msb_neg m h0 hm)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight]
    have key : ∀ j, j < 64 → ((18446744073709551615#64).getLsbD j && (18446744073709551614#64).getLsbD j) = decide (j ≠ 0) := by
      decide
    have k1 : ∀ j, j < 64 → (1#64).getLsbD j = decide (j = 0) := by decide
    rw [key i hi, k1 i hi]
    by_cases h5 : i = 0
    · subst h5
      have hb : (-m).getLsbD 63 = true := by simpa using msb_neg m h0 hm
      simp [hb]
    · simp [h5]

end Fv256.TopMath
