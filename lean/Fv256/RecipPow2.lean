/-!
# The power-of-two test of `Reciprocal`, per 64-bit limb (Extracted-free)

The code tests `m0 | m1 | m2 | (m3 & (m3 - 1)) == 0` (with `m3 ≠ 0`); this is `m = 2^log2 m`.
-/

namespace Fv256.F

theorem pow2_limbs (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64)
    (h3 : m3 ≠ 0) :
    (m0 ||| m1 ||| m2 ||| (m3 &&& (m3 - 1))) = 0 ↔
      m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 = 2 ^ Nat.log2 (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) := by
  constructor
  · intro h
    simp only [Nat.or_eq_zero_iff] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h4⟩ := h
    obtain ⟨k, hk⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo h3).1 h4
    subst h0 h1 h2
    have e : 0 + 2 ^ 64 * 0 + 2 ^ 128 * 0 + 2 ^ 192 * m3 = 2 ^ (192 + k) := by
      rw [hk, Nat.pow_add]; omega
    rw [e, Nat.log2_two_pow]
  · intro h
    generalize hL : Nat.log2 (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) = L at h
    have hge : 2 ^ 192 ≤ 2 ^ L := by
      have : 2 ^ 192 * 1 ≤ 2 ^ 192 * m3 := Nat.mul_le_mul_left _ (by omega)
      omega
    have hL192 : 192 ≤ L := by
      apply Nat.lt_of_not_ge; intro hn
      have := Nat.pow_lt_pow_right (show 1 < 2 by decide) (show L < 192 by omega)
      omega
    have e : 2 ^ L = 2 ^ 192 * 2 ^ (L - 192) := by
      rw [← Nat.pow_add, show 192 + (L - 192) = L by omega]
    rw [e] at h
    obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (L - 192) := ⟨_, rfl⟩
    rw [← hP] at h
    have hm3 : m3 = P := by omega
    have h0 : m0 = 0 := by omega
    have h1 : m1 = 0 := by omega
    have h2 : m2 = 0 := by omega
    subst h0 h1 h2
    simp only [Nat.zero_or]
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo h3).2 ⟨L - 192, by rw [hm3, hP]⟩

end Fv256.F
