import Fv256.Proofs.Common.RecipChain1

namespace Fv256.F
open Fv256.RecipMath
set_option exponentiation.threshold 1024

/-- one-sided Newton bound: `A (r' Y - A) ≤ Y E` as soon as `A T - r² Y ≥ -E` -/
theorem step_upper (A Y r T r' E : Int) (h : r' = 2 * r - T) (hY : 0 < Y)
    (hT : -E ≤ A * T - r * r * Y) : A * (r' * Y - A) ≤ Y * E := by
  have hid := step_id A Y r T r' h
  have hsq := mul_self_nonneg' (A - r * Y)
  have h1 : Y * (-E) ≤ Y * (A * T - r * r * Y) := Int.mul_le_mul_of_nonneg_left hT (Int.le_of_lt hY)
  have e1 : Y * (-E) = -(Y * E) := by grind
  have e2 : A * (r' * Y - A) = -(A * (A - r' * Y)) := by grind
  rw [e2]
  generalize A * (A - r' * Y) = R at *
  generalize (A - r * Y) * (A - r * Y) = P at *
  generalize Y * (A * T - r * r * Y) = Q at *
  generalize Y * E = YE at *
  omega

theorem r1_special (y : Nat) (hc : yw y 3 = 2 ^ 63) : recipR1 y = 2 ^ 64 - 1 := by
  have hyh : yw y 3 / 2 ^ 32 = 2 ^ 31 := by rw [hc]
  have e0 := recipR0_val y hyh
  have e1 : recipT1 y = 2 ^ 63 - 2 ^ 32 := by unfold recipT1; rw [e0, hc]; try decide
  have e2 : recipR1raw y = 0 := by unfold recipR1raw; rw [e0, e1]; try decide
  unfold recipR1; rw [e2, hc]; try rw [if_pos (by decide)]

/-- the signed stage-2 value `2 r1 2^64 - 2 e`: Newton window and one-sided bound -/
theorem stage2_int (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    -(2 ^ 266 : Int) ≤ 2 ^ 383 - (2 * ((recipR1 y : Int) * 2 ^ 64) - 2 * (stage2e (recipR1 y) (yw y 2) (yw y 3) : Int)) * y ∧
    2 ^ 383 - (2 * ((recipR1 y : Int) * 2 ^ 64) - 2 * (stage2e (recipR1 y) (yw y 2) (yw y 3) : Int)) * y ≤ 2 ^ 266 ∧
    (2 * ((recipR1 y : Int) * 2 ^ 64) - 2 * (stage2e (recipR1 y) (yw y 2) (yw y 3) : Int)) * y ≤ 2 ^ 383 + 8 * y := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  obtain ⟨r1lt, r1a, r1b⟩ := r1_spec y hy1 hy2
  have hw := stage2e_win (recipR1 y) (yw y 0) (yw y 1) (yw y 2) (yw y 3) r1lt b0 b1 b2 b3
  rw [← hd] at hw
  generalize recipR1 y = r1 at *
  generalize stage2e r1 (yw y 2) (yw y 3) = e at *
  have hwI : 2 ^ 256 * (e : Int) ≤ (r1 : Int) * r1 * y ∧ (r1 : Int) * r1 * y < 2 ^ 256 * e + 3 * 2 ^ 256 := by
    exact ⟨by exact_mod_cast hw.1, by exact_mod_cast hw.2⟩
  have hT := T2win (r1 : Int) (e : Int) (y : Int) hwI
  have hdI : -(2 ^ 324 : Int) ≤ 2 ^ 383 - ((r1 : Int) * 2 ^ 64) * y ∧ 2 ^ 383 - ((r1 : Int) * 2 ^ 64) * y ≤ 2 ^ 324 := by
    have e1 : ((r1 : Int) * 2 ^ 64) * y = 2 ^ 64 * ((r1 : Int) * y) := by grind
    have a1 : (2 ^ 319 : Int) ≤ (r1 : Int) * y + 2 ^ 260 := by exact_mod_cast r1a
    have a2 : (r1 : Int) * y ≤ 2 ^ 319 + 2 ^ 260 := by exact_mod_cast r1b
    rw [e1]
    generalize (r1 : Int) * y = P at *
    have k : (2 : Int) ^ 383 = 2 ^ 64 * 2 ^ 319 := by decide
    have k2 : (2 : Int) ^ 64 * 2 ^ 260 = 2 ^ 324 := by decide
    have g1 : 2 ^ 64 * (2 ^ 319 : Int) ≤ 2 ^ 64 * (P + 2 ^ 260) := Int.mul_le_mul_of_nonneg_left a1 (by decide)
    have g2 : 2 ^ 64 * P ≤ 2 ^ 64 * ((2 : Int) ^ 319 + 2 ^ 260) := Int.mul_le_mul_of_nonneg_left a2 (by decide)
    have g3 : 2 ^ 64 * (P + 2 ^ 260) = 2 ^ 64 * P + 2 ^ 324 := by grind
    have g4 : 2 ^ 64 * ((2 : Int) ^ 319 + 2 ^ 260) = 2 ^ 64 * 2 ^ 319 + 2 ^ 324 := by grind
    rw [k]
    constructor <;> omega
  have hyI : (2 : Int) ^ 255 ≤ y ∧ (y : Int) < 2 ^ 256 := by constructor <;> omega
  have hs := stage2 y ((r1 : Int) * 2 ^ 64) _ (2 * e) hyI rfl hT hdI
  refine ⟨hs.1, hs.2, ?_⟩
  have hup := step_upper (2 ^ 383) y ((r1 : Int) * 2 ^ 64) (2 * e) _ (8 * 2 ^ 383) rfl (by omega) (by have := hT.1; omega)
  generalize (2 * ((r1 : Int) * 2 ^ 64) - 2 * (e : Int)) * y = X at *
  have e8 : (y : Int) * (8 * 2 ^ 383) = 2 ^ 383 * (8 * y) := by grind
  rw [e8] at hup
  have := Int.le_of_mul_le_mul_left hup (by decide)
  omega

/-- `stage2e` for the special `r1 = 2^64 - 1`, `y3 = 2^63` -/
theorem stage2e_special (y2 : Nat) (h : y2 < 2 ^ 64) :
    stage2e (2 ^ 64 - 1) y2 (2 ^ 63) = (2 ^ 64 - 2) * 2 ^ 63 + (2 ^ 63 + (2 ^ 64 - 2) * y2) / 2 ^ 64 := by
  unfold stage2e
  have e1 : (2 ^ 64 - 1) * (2 ^ 64 - 1) / 2 ^ 64 = 2 ^ 64 - 2 := by decide
  have e2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) % 2 ^ 64 = 1 := by decide
  rw [e1, e2, Nat.one_mul, Nat.one_mul, Nat.div_eq_of_lt h]

theorem r2_spec (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    recipR2 y < 2 ^ 128 ∧ 2 ^ 383 ≤ recipR2 y * y + 2 ^ 266 ∧ recipR2 y * y ≤ 2 ^ 383 + 2 ^ 266 := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  obtain ⟨r1lt, -, -⟩ := r1_spec y hy1 hy2
  obtain ⟨w1, w2, w3⟩ := stage2_int y hy1 hy2
  have hy3 : 2 ^ 63 ≤ yw y 3 := by numr; omega
  by_cases hc : yw y 3 = 2 ^ 63
  · have hr1 := r1_special y hc
    have he : stage2e (recipR1 y) (yw y 2) (yw y 3) = (2 ^ 64 - 2) * 2 ^ 63 + (2 ^ 63 + (2 ^ 64 - 2) * yw y 2) / 2 ^ 64 := by
      rw [hr1, hc]; exact stage2e_special _ b2
    unfold recipR2 recipR2raw
    rw [he, hr1, hc]
    rw [he, hr1] at w1 w2 w3
    have hdm := Nat.div_add_mod (2 ^ 63 + (2 ^ 64 - 2) * yw y 2) (2 ^ 64)
    have hlt := Nat.mod_lt (2 ^ 63 + (2 ^ 64 - 2) * yw y 2) (Nat.two_pow_pos 64)
    generalize (2 ^ 63 + (2 ^ 64 - 2) * yw y 2) / 2 ^ 64 = u at *
    generalize (2 ^ 63 + (2 ^ 64 - 2) * yw y 2) % 2 ^ 64 = rr at *
    by_cases h2 : yw y 2 = 0
    · rw [h2] at hdm
      have hu : u = 0 := by numr; omega
      subst hu
      have hg : (2 * ((2 ^ 64 - 1) * 2 ^ 64) + 2 ^ 128 - 2 * ((2 ^ 64 - 2) * 2 ^ 63 + 0) % 2 ^ 128) % 2 ^ 128 = 0 := by decide
      rw [hg, if_pos ⟨rfl, by omega⟩]
      numr
      refine ⟨by omega, by omega, by omega⟩
    · have hu : 1 ≤ u := by numr; omega
      have hu2 : u < 2 ^ 64 := by numr; omega
      have hraw : (2 * ((2 ^ 64 - 1) * 2 ^ 64) + 2 ^ 128 - 2 * ((2 ^ 64 - 2) * 2 ^ 63 + u) % 2 ^ 128) % 2 ^ 128 = 2 ^ 128 - 2 * u := by
        numr; omega
      rw [hraw, if_neg (by numr; omega)]
      generalize hX : (2 * (((2 ^ 64 - 1 : Nat) : Int) * 2 ^ 64) - 2 * (((2 ^ 64 - 2) * 2 ^ 63 + u : Nat) : Int)) = X at w1 w2 w3
      have hR : X = ((2 ^ 128 - 2 * u : Nat) : Int) := by
        rw [← hX]; numr; omega
      have hlt128 : 2 ^ 128 - 2 * u < 2 ^ 128 := by numr; omega
      subst hR
      generalize 2 ^ 128 - 2 * u = R at *
      refine ⟨hlt128, ?_, ?_⟩
      · have h2 : (2 : Int) ^ 383 ≤ (R : Int) * y + 2 ^ 266 := by omega
        exact_mod_cast h2
      · have h2 : (R : Int) * y ≤ 2 ^ 383 + 2 ^ 266 := by omega
        exact_mod_cast h2
  · have hy3' : 2 ^ 63 < yw y 3 := by omega
    have nz : 2 * yw y 3 % 2 ^ 64 ≠ 0 := by numr; omega
    unfold recipR2 recipR2raw
    generalize recipR1 y = r1 at *
    generalize stage2e r1 (yw y 2) (yw y 3) = e at *
    generalize hX : (2 * ((r1 : Int) * 2 ^ 64) - 2 * (e : Int)) = X at w1 w2 w3
    have hy256 : (2 : Int) ^ 255 + 2 ^ 192 ≤ y := by numr; omega
    have hy0 : (0 : Int) ≤ y := Int.natCast_nonneg _
    have hXpos : 0 < X := by
      apply Int.lt_of_not_ge; intro hn
      have := Int.mul_le_mul_of_nonneg_right hn hy0
      have h0 : (0 : Int) * y = 0 := Int.zero_mul _
      numr
      omega
    have hXlt : X < 2 ^ 128 := by
      apply Int.lt_of_not_ge; intro hn
      have := Int.mul_le_mul_of_nonneg_right hn hy0
      numr
      omega
    have hR : ((2 * (r1 * 2 ^ 64) + 2 ^ 128 - 2 * e % 2 ^ 128) % 2 ^ 128 : Nat) = X := by
      rw [← hX]; numr; omega
    have hne : ¬ ((2 * (r1 * 2 ^ 64) + 2 ^ 128 - 2 * e % 2 ^ 128) % 2 ^ 128 = 0 ∧ 2 * yw y 3 % 2 ^ 64 = 0) := by
      intro h; exact nz h.2
    rw [if_neg hne]
    generalize (2 * (r1 * 2 ^ 64) + 2 ^ 128 - 2 * e % 2 ^ 128) % 2 ^ 128 = R at *
    subst hR
    refine ⟨by omega, ?_, ?_⟩
    · have h2 : (2 : Int) ^ 383 ≤ (R : Int) * y + 2 ^ 266 := by omega
      exact_mod_cast h2
    · have h2 : (R : Int) * y ≤ 2 ^ 383 + 2 ^ 266 := by omega
      exact_mod_cast h2

end Fv256.F
