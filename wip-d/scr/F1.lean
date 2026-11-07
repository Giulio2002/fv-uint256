import Janus
import Fv256.Spec
import Fv256.Util

namespace Fv256.D

theorem f64_bits (q r t Y y0 y1 y2 y3 : Nat) (ht1 : 12 ≤ t) (ht2 : t ≤ 203) (hr : r < 2 ^ t) (hq : q < 2 ^ 52)
    (hY : Y = q * 2 ^ 204 + r * 2 ^ (204 - t))
    (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Y) :
    y3 / 4096 = q ∧
    (2048 ≤ y3 % 4096 ↔ 2 ^ (t - 1) ≤ r) ∧
    ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ r % 2 ^ (t - 1) ≠ 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hh : 2 ^ s * 2 ^ (204 - (s + 1)) = 2 ^ 203 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hr2 : r < 2 * 2 ^ s := by rw [Nat.pow_succ] at hr; omega
  clear hr
  generalize 2 ^ s = h at *
  generalize 2 ^ (204 - (s + 1)) = Pm at *
  have hp : 0 < Pm := by
    rcases Nat.eq_zero_or_pos Pm with h | h
    · subst h; simp at hh
    · exact h
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · subst h'; simp at hh
    · exact h'
  have hu : r * Pm < 2 ^ 204 := by
    have : r * Pm < 2 * h * Pm := Nat.mul_lt_mul_of_pos_right hr2 hp
    have e : 2 * h * Pm = 2 ^ 204 := by rw [Nat.mul_assoc, hh]
    omega
  generalize hU : r * Pm = u at *
  have e3 : y3 = Y / 2 ^ 192 := by omega
  have eY : y3 / 4096 = q ∧ y3 % 4096 = u / 2 ^ 192 := by omega
  refine ⟨eY.1, ?_, ?_⟩
  · rw [eY.2]
    have : 2048 ≤ u / 2 ^ 192 ↔ 2 ^ 203 ≤ u := by omega
    rw [this, ← hh, ← hU]
    exact Nat.mul_le_mul_right_iff hp
  · have : (y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ u % 2 ^ 203 ≠ 0 := by omega
    rw [this, ← hh, ← hU, Nat.mul_mod_mul_right]
    constructor
    · intro hne hz; apply hne; rw [hz]; simp
    · intro hne hz; apply hne
      rcases Nat.mul_eq_zero.1 hz with h | h
      · exact h
      · omega
end Fv256.D
