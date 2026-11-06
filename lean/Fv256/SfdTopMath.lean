import Fv256.SpecI
import Fv256.UtilI

/-! Pure lemmas for the top level of `SetFromDecimal` (arm64): the branch-free `s[1:]` pointer mask, etc. -/

namespace Fv256.TopMath

open Fv256.I Fv256.I.Fv256.I

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

theorem plusEnd_le (b : Nat → Nat) (n : Nat) : plusEnd b n ≤ n := by
  unfold plusEnd; split <;> omega

theorem startPos_end (b : Nat → Nat) (n : Nat) (h : plusEnd b n = n) : startPos b n = n := by
  unfold startPos
  rw [h]
  simp [zerosFrom]

theorem startPos_nz (b : Nat → Nat) (n : Nat) (h : plusEnd b n < n) (hb : b (plusEnd b n) ≠ 48) :
    startPos b n = plusEnd b n := by
  obtain ⟨f, hf⟩ : ∃ f, n - plusEnd b n = f + 1 := ⟨n - plusEnd b n - 1, by omega⟩
  unfold startPos
  rw [hf]
  simp only [zerosFrom]
  simp [hb, h]
  intro h'; omega

theorem startPos_a (b : Nat → Nat) (n i : Nat) (h : plusEnd b n + i < n) (hb : b (plusEnd b n + i) ≠ 48)
    (hz : ∀ k, k < i → b (plusEnd b n + k) = 48) : startPos b n = plusEnd b n + i := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := startPos_spec b n
  have hl := startPos_lead b n (by omega)
  have hlt : plusEnd b n < n := by omega
  by_cases hc : startPos b n < plusEnd b n + i
  · have h48 : b (startPos b n) = 48 := by
      have := hz (startPos b n - plusEnd b n) (by omega)
      rw [show plusEnd b n + (startPos b n - plusEnd b n) = startPos b n by omega] at this
      exact this
    rcases hl with hl | hl
    · exact absurd h48 hl
    · omega
  · by_cases hd : startPos b n > plusEnd b n + i
    · have := s5 (plusEnd b n + i) (by omega) hd
      exact absurd this hb
    · omega

theorem startPos_b (b : Nat → Nat) (n : Nat) (h : plusEnd b n < n) (hz : ∀ k, plusEnd b n ≤ k → k < n → b k = 48) :
    startPos b n = n - 1 := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := startPos_spec b n
  have hl := startPos_lead b n h
  have := s4 h
  rcases hl with hl | hl
  · exact absurd (hz _ s2 this) hl
  · exact hl

end Fv256.TopMath
