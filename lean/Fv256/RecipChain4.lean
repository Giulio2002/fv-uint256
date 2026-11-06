import Fv256.RecipChain3

namespace Fv256.F
open Fv256.RecipMath
set_option exponentiation.threshold 1024

theorem mul64_lt (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 := by
  have := Nat.mul_lt_mul'' ha hb
  simpa [← Nat.pow_add] using this

/-- `R3² y = V4 2^192 + D` with `D < 2^258` -/
theorem v4_split (y : Nat) (hy2 : y < 2 ^ 256) (hR3 : recipR3 y < 2 ^ 192) :
    ∃ D, D < 2 ^ 258 ∧ recipR3 y * recipR3 y * y = recipV4 y * 2 ^ 192 + D := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  obtain ⟨hs, s0, s1, s2, s3, s4, s5⟩ := rsqw_sum6 (recipR3 y) hR3
  unfold recipV4
  generalize recipR3 y = R at *
  generalize rsqw R 0 = w0 at *
  generalize rsqw R 1 = w1 at *
  generalize rsqw R 2 = w2 at *
  generalize rsqw R 3 = w3 at *
  generalize rsqw R 4 = w4 at *
  generalize rsqw R 5 = w5 at *
  generalize yw y 0 = y0 at *
  generalize yw y 1 = y1 at *
  generalize yw y 2 = y2 at *
  generalize yw y 3 = y3 at *
  refine ⟨w0 * y0 + 2 ^ 64 * (w0 * y1 + w1 * y0) + 2 ^ 128 * (w0 * y2 + w1 * y1 + w2 * y0), ?_, ?_⟩
  · have p00 := mul64_lt w0 y0 s0 b0
    have p01 := mul64_lt w0 y1 s0 b1
    have p10 := mul64_lt w1 y0 s1 b0
    have p02 := mul64_lt w0 y2 s0 b2
    have p11 := mul64_lt w1 y1 s1 b1
    have p20 := mul64_lt w2 y0 s2 b0
    generalize w0 * y0 = a00 at *
    generalize w0 * y1 = a01 at *
    generalize w1 * y0 = a10 at *
    generalize w0 * y2 = a02 at *
    generalize w1 * y1 = a11 at *
    generalize w2 * y0 = a20 at *
    numr
    omega
  · rw [hs, hd]
    grind

theorem r4pre_spec (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    2 ^ 574 ≤ recipR4pre y * y + y + 2 ^ 200 ∧ recipR4pre y * y ≤ 2 ^ 574 + 2 ^ 200 ∧ recipR4pre y < 2 ^ 320 := by
  obtain ⟨hR3, r3a, r3b, -⟩ := r3_spec y hy1 hy2
  obtain ⟨D, hD, hsp⟩ := v4_split y hy2 hR3
  unfold recipR4pre
  generalize recipV4 y = V at *
  generalize recipR3 y = u at *
  have hK := Nat.div_add_mod (V + 2 ^ 128 - 1) (2 ^ 128)
  have hKl := Nat.mod_lt (V + 2 ^ 128 - 1) (Nat.two_pow_pos 128)
  generalize (V + 2 ^ 128 - 1) / 2 ^ 128 = K at *
  generalize (V + 2 ^ 128 - 1) % 2 ^ 128 = rr at *
  have hdI : -(2 ^ 260 : Int) ≤ 2 ^ 447 - (u : Int) * y ∧ 2 ^ 447 - (u : Int) * y ≤ 2 ^ 260 := by
    have a1 : (2 ^ 447 : Int) ≤ (u : Int) * y + 2 ^ 260 := by exact_mod_cast r3a
    have a2 : (u : Int) * y ≤ 2 ^ 447 + 2 ^ 260 := by exact_mod_cast r3b
    constructor <;> omega
  have hsI : (u : Int) * u * y = V * 2 ^ 192 + D := by exact_mod_cast hsp
  have hKI : (u : Int) * u * y - D ≤ 2 ^ 320 * K ∧ 2 ^ 320 * (K : Int) < u * u * y - D + 2 ^ 320 := by
    rw [hsI]
    have e1 : (V : Int) * 2 ^ 192 + D - D = 2 ^ 192 * V := by grind
    rw [e1]
    have g1 : (2 : Int) ^ 192 * V ≤ 2 ^ 192 * ((K : Int) * 2 ^ 128) := Int.mul_le_mul_of_nonneg_left (by omega) (by decide)
    have g2 : (2 : Int) ^ 192 * (K * 2 ^ 128) = 2 ^ 320 * K := by grind
    have g3 : (2 : Int) ^ 192 * ((K : Int) * 2 ^ 128) < 2 ^ 192 * (V + 2 ^ 128) := Int.mul_lt_mul_of_pos_left (by omega) (by decide)
    have g4 : (2 : Int) ^ 192 * ((V : Int) + 2 ^ 128) = 2 ^ 192 * V + 2 ^ 320 := by grind
    constructor <;> omega
  have hyI : (2 : Int) ^ 255 ≤ y ∧ (y : Int) < 2 ^ 256 := by constructor <;> omega
  have hst := stage4 y u D K hyI hdI ⟨by omega, by exact_mod_cast hD⟩ hKI
  -- positivity of u 2^128 - K
  have hy0 : (0 : Int) ≤ y := Int.natCast_nonneg _
  have hpos : 0 < (u : Int) * 2 ^ 128 - K := by
    apply Int.lt_of_not_ge; intro hn
    have := Int.mul_le_mul_of_nonneg_right hn hy0
    have h0 : (0 : Int) * y = 0 := Int.zero_mul _
    have := hst.1
    numr
    omega
  have hR : ((u * 2 ^ 256 + 2 ^ 448 - V) % 2 ^ 448 / 2 ^ 128 : Nat) = u * 2 ^ 128 - K := by
    have hVK : V ≤ K * 2 ^ 128 := by omega
    have hKu : K < u * 2 ^ 128 := by omega
    numr
    omega
  rw [hR]
  have hcast : ((u * 2 ^ 128 - K : Nat) : Int) = (u : Int) * 2 ^ 128 - K := by
    have hKu : K < u * 2 ^ 128 := by omega
    omega
  have hlt : u * 2 ^ 128 - K < 2 ^ 320 := by numr; omega
  obtain ⟨R, hRdef⟩ : ∃ R, R = u * 2 ^ 128 - K := ⟨_, rfl⟩
  rw [← hRdef] at hcast hlt ⊢
  rw [← hcast] at hst
  refine ⟨?_, ?_, hlt⟩
  · have h2 : (2 : Int) ^ 574 ≤ (R : Int) * y + y + 2 ^ 200 := by omega
    exact_mod_cast h2
  · have h2 : (R : Int) * y ≤ 2 ^ 574 + 2 ^ 200 := by omega
    exact_mod_cast h2

theorem r4_spec (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    2 ^ 574 / y - 1 ≤ recipR4 y ∧ recipR4 y ≤ 2 ^ 574 / y ∧ recipR4 y < 2 ^ 319 := by
  obtain ⟨a, b, c⟩ := r4pre_spec y hy1 hy2
  have hpos : 1 ≤ recipR4pre y := by
    apply Nat.lt_of_not_ge; intro hn
    have : recipR4pre y = 0 := by omega
    rw [this] at a
    numr
    omega
  have e : recipR4 y = if 2 ^ 574 < recipR4pre y * y then recipR4pre y - 1 else recipR4pre y := by
    unfold recipR4
    by_cases h : 2 ^ 574 < recipR4pre y * y
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
  have hadj := adjust (2 ^ 574) y (recipR4pre y) (2 ^ 200) (by numr; omega) a b
  rw [← e] at hadj
  refine ⟨hadj.1, hadj.2, ?_⟩
  have : 2 ^ 574 / y < 2 ^ 319 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    numr
    omega
  omega

end Fv256.F
