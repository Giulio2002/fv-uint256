import Janus
import Fv256.Proofs.Legacy.B
import Fv256.Spec.Float64

namespace Fv256.Float64Bridge

open Janus.Float

/-- the rounding decision of `roundUp` for ties-to-even, in the readable form used by `Spec.float64Bits` -/
theorem round_eq (k rem m : Nat) (hm : 0 < m) :
    (if (if rem = 0 then false else decide (2 * rem > m) || (decide (2 * rem = m) && decide (k % 2 = 1))) = true then k + 1 else k) =
    (if rem * 2 > m ∨ (rem * 2 = m ∧ k % 2 = 1) then k + 1 else k) := by
  by_cases h : rem = 0
  · subst h; simp only [ite_true, Bool.false_eq_true, ite_false]; split <;> omega
  · simp only [h, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    have : (2 * rem > m ∨ 2 * rem = m ∧ k % 2 = 1) ↔ (rem * 2 > m ∨ (rem * 2 = m ∧ k % 2 = 1)) := by
      rw [Nat.mul_comm 2 rem]
    simp only [this]

/-- THE BRIDGE: the readable `Spec.float64Bits` is the Janus IEEE `convertFromInt` (round-to-nearest-even into binary64) used by the
implementation-shaped statement `Fv256.B.float64BitsNearest`, for every 256-bit number. -/
theorem float64Bits_eq (x : Nat) (hx : x < 2 ^ 256) : Fv256.Spec.float64Bits x = Fv256.B.float64BitsNearest x := by
  unfold Fv256.B.float64BitsNearest fromInt
  by_cases h0 : x = 0
  · subst h0; decide
  have hI : (x : Int) ≠ 0 := by omega
  simp only [hI, ite_false]
  have hlog : Nat.log2 x < 256 := by
    rw [Nat.log2_lt (by omega)]; exact hx
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le h0
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  unfold Fv256.Spec.float64Bits
  simp only [h0, ite_false]
  simp only [Int.natAbs_natCast, round, roundUnits, roundAt, biasedExp, binary64, Fmt.emin, Fmt.bias, Fmt.expMax, pack, Fmt.signBit]
  have hq : max ((x.log2 : Int) + 0) (1 - ((2 ^ (11 - 1) - 1 : Nat) : Int)) - ((52 : Nat) : Int) = (x.log2 : Int) - 52 := by
    have h1023 : (2 ^ (11 - 1) - 1 : Nat) = 1023 := by decide
    rw [h1023]; omega
  simp only [hq]
  by_cases hL : x.log2 ≤ 52
  · have hA : (x.log2 : Int) - 52 ≤ 0 := by omega
    have hk1 : 2 ^ 52 ≤ x * 2 ^ (52 - x.log2) := by
      calc 2 ^ 52 = 2 ^ x.log2 * 2 ^ (52 - x.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ x * 2 ^ (52 - x.log2) := Nat.mul_le_mul_right _ hlo
    have hk2 : x * 2 ^ (52 - x.log2) < 2 ^ 53 := by
      calc x * 2 ^ (52 - x.log2) < 2 ^ (x.log2 + 1) * 2 ^ (52 - x.log2) := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
        _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
    have hz : (0 - ((x.log2 : Int) - 52)).toNat = 52 - x.log2 := by omega
    have hne : x * 2 ^ (52 - x.log2) ≠ 2 ^ (52 + 1) := Nat.ne_of_lt hk2
    have hnl : ¬ (x * 2 ^ (52 - x.log2) < 2 ^ 52) := by omega
    have hxn : decide ((x : Int) < 0) = false := by simp
    have h1023 : (2 ^ (11 - 1) - 1 : Nat) = 1023 := by decide
    have hb : ((x.log2 : Int) - 52 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)).toNat = x.log2 + 1023 := by omega
    have hnov : ¬ (((x.log2 : Int) - 52 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)) ≥ ((2048 - 1 : Nat) : Int)) := by omega
    simp only [hA, hL, ite_true, hz, Nat.reducePow, hne, ite_false, hnl, hxn, h1023, hb, hnov]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
  · have hB : ¬ ((x.log2 : Int) - 52 ≤ 0) := by omega
    have hxn : decide ((x : Int) < 0) = false := by simp
    have h1023 : (2 ^ (11 - 1) - 1 : Nat) = 1023 := by decide
    have hs' : ((x.log2 : Int) - 52).toNat = x.log2 - 52 := by omega
    have hpos : 0 < 2 ^ (x.log2 - 52) := Nat.two_pow_pos _
    have hkept1 : 2 ^ 52 ≤ x / 2 ^ (x.log2 - 52) := by
      rw [Nat.le_div_iff_mul_le hpos]
      calc 2 ^ 52 * 2 ^ (x.log2 - 52) = 2 ^ x.log2 := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ x := hlo
    have hkept2 : x / 2 ^ (x.log2 - 52) < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      calc x < 2 ^ (x.log2 + 1) := hhi
        _ = 2 ^ 53 * 2 ^ (x.log2 - 52) := by rw [← Nat.pow_add]; congr 1; omega
    simp only [hB, hL, ite_false, hxn, h1023, Nat.reducePow, roundUp, Int.sub_zero, hs', round_eq _ _ _ hpos]
    generalize hRd : (if x % 2 ^ (x.log2 - 52) * 2 > 2 ^ (x.log2 - 52) ∨
        x % 2 ^ (x.log2 - 52) * 2 = 2 ^ (x.log2 - 52) ∧ x / 2 ^ (x.log2 - 52) % 2 = 1 then
        x / 2 ^ (x.log2 - 52) + 1 else x / 2 ^ (x.log2 - 52)) = R
    have hR1 : 2 ^ 52 ≤ R := by rw [← hRd]; split <;> omega
    have hR2 : R ≤ 2 ^ 53 := by rw [← hRd]; split <;> omega
    by_cases hR3 : R = 2 ^ 53
    · have hb : ((x.log2 : Int) - 52 + 1 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)).toNat = x.log2 + 1 + 1023 := by omega
      have hnov : ¬ (((x.log2 : Int) - 52 + 1 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)) ≥ ((2048 - 1 : Nat) : Int)) := by omega
      have e1 : (2 : Nat) ^ 53 / 2 = 2 ^ 52 := by decide
      have e2 : (2 : Nat) ^ 53 = 2 ^ (52 + 1) := by decide
      have e3 : ¬ ((2 : Nat) ^ 52 < 4503599627370496) := by decide
      have e4 : (2 : Nat) ^ 52 % 4503599627370496 = 0 := by decide
      simp only [hR3, e1, ← e2, ite_true, hb, hnov, ite_false, e3, e4, Bool.false_eq_true]
      simp only [Nat.zero_add, Nat.add_zero]
    · have hb : ((x.log2 : Int) - 52 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)).toNat = x.log2 + 1023 := by omega
      have hnov : ¬ (((x.log2 : Int) - 52 + ((52 : Nat) : Int) + ((1023 : Nat) : Int)) ≥ ((2048 - 1 : Nat) : Int)) := by omega
      have hnl : ¬ (R < 4503599627370496) := by omega
      simp only [hR3, ite_false, hb, hnov, hnl, Bool.false_eq_true, Nat.zero_add]

/-- The same for the 256-bit number stored at `a` in memory. -/
theorem float64Bits_eq_mem (m : Janus.Arm64.Memory) (a : Nat) :
    Fv256.Spec.float64Bits (m.readLE a 32) = Fv256.B.float64BitsNearest (m.readLE a 32) := by
  apply float64Bits_eq
  have := Janus.Arm64.Memory.readLE_lt m a 32
  have h : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  omega

end Fv256.Float64Bridge
