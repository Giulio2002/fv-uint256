import Fv256.Proofs.Common.RecipChain2

namespace Fv256.F
open Fv256.RecipMath
set_option exponentiation.threshold 1024

theorem rsqw_sum4 (R : Nat) (h : R < 2 ^ 128) :
    R * R = rsqw R 0 + 2 ^ 64 * rsqw R 1 + 2 ^ 128 * rsqw R 2 + 2 ^ 192 * rsqw R 3 ∧
    rsqw R 0 < 2 ^ 64 ∧ rsqw R 1 < 2 ^ 64 ∧ rsqw R 2 < 2 ^ 64 ∧ rsqw R 3 < 2 ^ 64 := by
  have hlt : R * R < 2 ^ 256 := by
    have := Nat.mul_lt_mul'' h h
    simpa [← Nat.pow_add] using this
  unfold rsqw
  numr
  generalize R * R = X at *
  omega

theorem rsqw_sum6 (R : Nat) (h : R < 2 ^ 192) :
    R * R = rsqw R 0 + 2 ^ 64 * rsqw R 1 + 2 ^ 128 * rsqw R 2 + 2 ^ 192 * rsqw R 3 + 2 ^ 256 * rsqw R 4 + 2 ^ 320 * rsqw R 5 ∧
    rsqw R 0 < 2 ^ 64 ∧ rsqw R 1 < 2 ^ 64 ∧ rsqw R 2 < 2 ^ 64 ∧ rsqw R 3 < 2 ^ 64 ∧ rsqw R 4 < 2 ^ 64 ∧ rsqw R 5 < 2 ^ 64 := by
  have hlt : R * R < 2 ^ 384 := by
    have := Nat.mul_lt_mul'' h h
    simpa [← Nat.pow_add] using this
  unfold rsqw
  numr
  generalize R * R = X at *
  omega

/-- the signed stage-3 value `2 R2 2^64 - 2 K`, `K = ⌈Q3 / 2^128⌉`: window and one-sided bound -/
theorem stage3_int (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    -(2 ^ 260 : Int) ≤ 2 ^ 447 - (2 * ((recipR2 y : Int) * 2 ^ 64) - 2 * (((recipQ3 y + 2 ^ 128 - 1) / 2 ^ 128 : Nat) : Int)) * y ∧
    2 ^ 447 - (2 * ((recipR2 y : Int) * 2 ^ 64) - 2 * (((recipQ3 y + 2 ^ 128 - 1) / 2 ^ 128 : Nat) : Int)) * y ≤ 2 ^ 260 ∧
    (2 * ((recipR2 y : Int) * 2 ^ 64) - 2 * (((recipQ3 y + 2 ^ 128 - 1) / 2 ^ 128 : Nat) : Int)) * y ≤ 2 ^ 447 + 6 * 2 ^ 129 := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  obtain ⟨r2lt, r2a, r2b⟩ := r2_spec y hy1 hy2
  obtain ⟨hs, s0, s1, s2, s3⟩ := rsqw_sum4 (recipR2 y) r2lt
  have hw := stage3q_win (rsqw (recipR2 y) 0) (rsqw (recipR2 y) 1) (rsqw (recipR2 y) 2) (rsqw (recipR2 y) 3)
    (yw y 0) (yw y 1) (yw y 2) (yw y 3) s0 s1 s2 s3 b0 b1 b2 b3
  rw [← hs, ← hd] at hw
  have hQ : recipQ3 y = stage3q (rsqw (recipR2 y) 0) (rsqw (recipR2 y) 1) (rsqw (recipR2 y) 2) (rsqw (recipR2 y) 3)
    (yw y 0) (yw y 1) (yw y 2) (yw y 3) := rfl
  rw [← hQ] at hw
  clear hQ hs s0 s1 s2 s3 b0 b1 b2 b3 h3
  generalize recipQ3 y = V at *
  generalize recipR2 y = R at *
  have hK := Nat.div_add_mod (V + 2 ^ 128 - 1) (2 ^ 128)
  have hKl := Nat.mod_lt (V + 2 ^ 128 - 1) (Nat.two_pow_pos 128)
  generalize (V + 2 ^ 128 - 1) / 2 ^ 128 = K at *
  generalize (V + 2 ^ 128 - 1) % 2 ^ 128 = rr at *
  have hwI : 2 ^ 192 * (V : Int) ≤ (R : Int) * R * y ∧ (R : Int) * R * y < 2 ^ 192 * V + 6 * 2 ^ 192 := by
    exact ⟨by exact_mod_cast hw.1, by exact_mod_cast hw.2⟩
  have hKI : ((K : Int) - 1) * 2 ^ 128 < V ∧ (V : Int) ≤ K * 2 ^ 128 := by
    have e : ((K : Int) - 1) * 2 ^ 128 = K * 2 ^ 128 - 2 ^ 128 := by grind
    rw [e]
    numr
    omega
  have hT := T3win (R : Int) (K : Int) (y : Int) (V : Int) hwI hKI
  have hdI : -(2 ^ 330 : Int) ≤ 2 ^ 447 - ((R : Int) * 2 ^ 64) * y ∧ 2 ^ 447 - ((R : Int) * 2 ^ 64) * y ≤ 2 ^ 330 := by
    have e1 : ((R : Int) * 2 ^ 64) * y = 2 ^ 64 * ((R : Int) * y) := by grind
    have a1 : (2 ^ 383 : Int) ≤ (R : Int) * y + 2 ^ 266 := by exact_mod_cast r2a
    have a2 : (R : Int) * y ≤ 2 ^ 383 + 2 ^ 266 := by exact_mod_cast r2b
    rw [e1]
    generalize (R : Int) * y = P at *
    have k : (2 : Int) ^ 447 = 2 ^ 64 * 2 ^ 383 := by decide
    have k2 : (2 : Int) ^ 64 * 2 ^ 266 = 2 ^ 330 := by decide
    have g1 : 2 ^ 64 * (2 ^ 383 : Int) ≤ 2 ^ 64 * (P + 2 ^ 266) := Int.mul_le_mul_of_nonneg_left a1 (by decide)
    have g2 : 2 ^ 64 * P ≤ 2 ^ 64 * ((2 : Int) ^ 383 + 2 ^ 266) := Int.mul_le_mul_of_nonneg_left a2 (by decide)
    have g3 : 2 ^ 64 * (P + 2 ^ 266) = 2 ^ 64 * P + 2 ^ 330 := by grind
    have g4 : 2 ^ 64 * ((2 : Int) ^ 383 + 2 ^ 266) = 2 ^ 64 * 2 ^ 383 + 2 ^ 330 := by grind
    rw [k]
    constructor <;> omega
  have hyI : (2 : Int) ^ 255 ≤ y ∧ (y : Int) < 2 ^ 256 := by constructor <;> omega
  have hs3 := stage3 y ((R : Int) * 2 ^ 64) _ (2 * K) hyI rfl hT hdI
  refine ⟨hs3.1, hs3.2, ?_⟩
  -- one-sided: A T - r^2 Y >= -6 * 2^320
  have hlow : -(6 * 2 ^ 320 : Int) ≤ 2 ^ 447 * (2 * K) - ((R : Int) * 2 ^ 64) * ((R : Int) * 2 ^ 64) * y := by
    have e1 : ((R : Int) * 2 ^ 64) * ((R : Int) * 2 ^ 64) * y = 2 ^ 128 * ((R : Int) * R * y) := by grind
    have e2 : (2 : Int) ^ 447 * (2 * K) = 2 ^ 320 * (K * 2 ^ 128) := by grind
    rw [e1, e2]
    have g1 : 2 ^ 128 * ((R : Int) * R * y) ≤ 2 ^ 128 * (2 ^ 192 * V + 6 * 2 ^ 192) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by decide)
    have g2 : 2 ^ 320 * (V : Int) ≤ 2 ^ 320 * (K * 2 ^ 128) := Int.mul_le_mul_of_nonneg_left hKI.2 (by decide)
    have g3 : 2 ^ 128 * (2 ^ 192 * (V : Int) + 6 * 2 ^ 192) = 2 ^ 320 * V + 6 * 2 ^ 320 := by grind
    generalize 2 ^ 128 * ((R : Int) * R * y) = P at *
    generalize 2 ^ 320 * (K * 2 ^ 128) = W at *
    generalize (2 : Int) ^ 320 * V = Z at *
    omega
  have hup := step_upper (2 ^ 447) y ((R : Int) * 2 ^ 64) (2 * K) _ (6 * 2 ^ 320) rfl (by omega) hlow
  generalize (2 * ((R : Int) * 2 ^ 64) - 2 * (K : Int)) * y = X at *
  have hyl : (y : Int) * (6 * 2 ^ 320) ≤ 2 ^ 447 * (6 * 2 ^ 129) := by
    have := Int.mul_le_mul_of_nonneg_right (show (y : Int) ≤ 2 ^ 256 by omega) (show (0 : Int) ≤ 6 * 2 ^ 320 by decide)
    have e : (2 : Int) ^ 256 * (6 * 2 ^ 320) = 2 ^ 447 * (6 * 2 ^ 129) := by decide
    omega
  have := Int.le_of_mul_le_mul_left (show 2 ^ 447 * (X - 2 ^ 447) ≤ 2 ^ 447 * (6 * 2 ^ 129) by omega) (by decide)
  omega

theorem r3_spec (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    recipR3 y < 2 ^ 192 ∧ 2 ^ 447 ≤ recipR3 y * y + 2 ^ 260 ∧ recipR3 y * y ≤ 2 ^ 447 + 2 ^ 260 ∧
    recipR3 y * y ≤ 2 ^ 447 + 2 ^ 132 := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  obtain ⟨r2lt, -, -⟩ := r2_spec y hy1 hy2
  obtain ⟨w1, w2, w3⟩ := stage3_int y hy1 hy2
  unfold recipR3
  generalize recipQ3 y = V at *
  generalize recipR2 y = R at *
  have hK := Nat.div_add_mod (V + 2 ^ 128 - 1) (2 ^ 128)
  have hKl := Nat.mod_lt (V + 2 ^ 128 - 1) (Nat.two_pow_pos 128)
  generalize (V + 2 ^ 128 - 1) / 2 ^ 128 = K at *
  generalize (V + 2 ^ 128 - 1) % 2 ^ 128 = rr at *
  generalize hX : (2 * ((R : Int) * 2 ^ 64) - 2 * (K : Int)) = X at w1 w2 w3
  have hy256 : (2 : Int) ^ 255 + 1 ≤ y := by numr; omega
  have hy0 : (0 : Int) ≤ y := Int.natCast_nonneg _
  have hXpos : 0 < X := by
    apply Int.lt_of_not_ge; intro hn
    have := Int.mul_le_mul_of_nonneg_right hn hy0
    have h0 : (0 : Int) * y = 0 := Int.zero_mul _
    numr
    omega
  have hXlt : X < 2 ^ 192 := by
    apply Int.lt_of_not_ge; intro hn
    have := Int.mul_le_mul_of_nonneg_right hn hy0
    numr
    omega
  have hR : (2 * ((R * 2 ^ 192 + 2 ^ 320 - V) % 2 ^ 320 / 2 ^ 128) % 2 ^ 192 : Nat) = X := by
    rw [← hX]; numr; omega
  generalize 2 * ((R * 2 ^ 192 + 2 ^ 320 - V) % 2 ^ 320 / 2 ^ 128) % 2 ^ 192 = R3 at *
  subst hR
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have h2 : (2 : Int) ^ 447 ≤ (R3 : Int) * y + 2 ^ 260 := by omega
    exact_mod_cast h2
  · have h2 : (R3 : Int) * y ≤ 2 ^ 447 + 2 ^ 260 := by omega
    exact_mod_cast h2
  · have h2 : (R3 : Int) * y ≤ 2 ^ 447 + 2 ^ 132 := by numr; omega
    exact_mod_cast h2

end Fv256.F
