import Fv256.Proofs.Common.RecipChainDefs

namespace Fv256.F
open Fv256.RecipMath
set_option exponentiation.threshold 1024

/-- evaluate literal powers/products before calling `omega` (omega on unevaluated big powers blows the kernel) -/
macro "numr" : tactic => `(tactic| try simp only [Nat.reducePow, Int.reducePow, Nat.reduceMul, Int.reduceMul, Nat.reduceAdd, Int.reduceAdd, Nat.reduceSub, Int.reduceSub, Int.reduceNeg] at *)

/-- `t1` is large enough that `2 (R0 - t1) < 2^64` when `yh > 2^31` -/
theorem t1_big (r0 yh y3 : Nat) (h1 : r0 * yh ≤ 2 ^ 63) (h2 : 2 ^ 31 + 1 ≤ yh) (h3 : 2 ^ 32 * yh ≤ y3) :
    2 ^ 32 * r0 < 2 ^ 63 + r0 * r0 * y3 / 2 ^ 64 := by
  apply Nat.lt_of_not_ge; intro hc
  have hdm := Nat.div_add_mod (r0 * r0 * y3) (2 ^ 64)
  have hlt := Nat.mod_lt (r0 * r0 * y3) (Nat.two_pow_pos 64)
  generalize r0 * r0 * y3 / 2 ^ 64 = t at *
  generalize r0 * r0 * y3 % 2 ^ 64 = rem at *
  have hP : r0 * r0 * y3 < 2 ^ 64 * (t + 1) := by omega
  have hc' : t + 1 + 2 ^ 63 ≤ 2 ^ 32 * r0 + 1 := by omega
  -- everything in Int
  have hP' : ((r0 : Int) * r0 * y3) < 2 ^ 64 * (t + 1) := by exact_mod_cast hP
  have hc'' : (t : Int) + 1 + 2 ^ 63 ≤ 2 ^ 32 * r0 + 1 := by exact_mod_cast hc'
  have hu : ((r0 : Int) * yh) ≤ 2 ^ 63 := by exact_mod_cast h1
  have hyh : (2 : Int) ^ 31 + 1 ≤ yh := by exact_mod_cast h2
  have hy3 : (2 : Int) ^ 32 * yh ≤ y3 := by exact_mod_cast h3
  have hr0 : (0 : Int) ≤ r0 := Int.natCast_nonneg _
  have hyh0 : (0 : Int) ≤ yh := by omega
  -- multiply hP' by yh
  have m1 : (yh : Int) * (r0 * r0 * y3) ≤ yh * (2 ^ 64 * (t + 1) - 1) := Int.mul_le_mul_of_nonneg_left (by omega) hyh0
  have m2 : (yh * r0 * r0 : Int) * (2 ^ 32 * yh) ≤ (yh * r0 * r0) * y3 :=
    Int.mul_le_mul_of_nonneg_left hy3 (Int.mul_nonneg (Int.mul_nonneg hyh0 hr0) hr0)
  have m3 : (2 ^ 64 * yh : Int) * (t + 1 + 2 ^ 63) ≤ (2 ^ 64 * yh) * (2 ^ 32 * r0 + 1) :=
    Int.mul_le_mul_of_nonneg_left hc'' (by omega)
  have sq := mul_self_nonneg' ((r0 : Int) * yh - 2 ^ 63)
  generalize hU : (r0 : Int) * yh = u at *
  have e1 : (yh * r0 * r0 : Int) * (2 ^ 32 * yh) = 2 ^ 32 * (u * u) := by rw [← hU]; grind
  have e2 : (yh : Int) * (r0 * r0 * y3) = (yh * r0 * r0) * y3 := by grind
  have e3 : (2 ^ 64 * yh : Int) * (2 ^ 32 * r0) = 2 ^ 96 * u := by rw [← hU]; grind
  have e4 : (2 ^ 64 * yh : Int) * (t + 1 + 2 ^ 63) = 2 ^ 64 * (yh * (t + 1)) + 2 ^ 127 * yh := by grind
  have e5 : (yh : Int) * (2 ^ 64 * (t + 1) - 1) = 2 ^ 64 * (yh * (t + 1)) - yh := by grind
  have e6 : (u - 2 ^ 63) * (u - 2 ^ 63) = u * u - 2 ^ 64 * u + 2 ^ 126 := by grind
  have e7 : (2 ^ 64 * yh : Int) * (2 ^ 32 * r0 + 1) = 2 ^ 96 * u + 2 ^ 64 * yh := by rw [← hU]; grind
  rw [e1] at m2
  rw [e4, e7] at m3
  rw [e2, e5] at m1
  generalize (yh : Int) * (t + 1) = W at *
  generalize (u - 2 ^ 63) * (u - 2 ^ 63) = Q at *
  have e8 : (2 : Int) ^ 32 * (2 ^ 64 * u) = 2 ^ 96 * u := by grind
  have e9 : (2 : Int) ^ 32 * 2 ^ 126 = 2 ^ 158 := by decide
  have e10 : (2 : Int) ^ 32 * (u * u - 2 ^ 64 * u + 2 ^ 126) = 2 ^ 32 * (u * u) - 2 ^ 96 * u + 2 ^ 158 := by grind
  have g := Int.mul_nonneg (show (0 : Int) ≤ 2 ^ 32 by decide) sq
  rw [e6, e10] at g
  have c1 : (2 : Int) ^ 127 * (2 ^ 31 + 1) = 2 ^ 158 + 2 ^ 127 := by decide
  have c2 : (2 : Int) ^ 64 * (2 ^ 31 + 1) = 2 ^ 95 + 2 ^ 64 := by decide
  have c3 : (2 : Int) ^ 127 * yh ≥ 2 ^ 127 * (2 ^ 31 + 1) := Int.mul_le_mul_of_nonneg_left hyh (by decide)
  clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hdm hP hP' hc hc' hc'' hlt
  numr
  omega


theorem yw_decomp (y : Nat) (h : y < 2 ^ 256) :
    y = yw y 0 + 2 ^ 64 * yw y 1 + 2 ^ 128 * yw y 2 + 2 ^ 192 * yw y 3 ∧
    yw y 0 < 2 ^ 64 ∧ yw y 1 < 2 ^ 64 ∧ yw y 2 < 2 ^ 64 ∧ yw y 3 < 2 ^ 64 ∧ yw y 3 = y / 2 ^ 192 := by
  unfold yw
  numr
  omega

theorem recipR0_facts (y : Nat) (hy3 : 2 ^ 63 ≤ yw y 3) (b3 : yw y 3 < 2 ^ 64) :
  recipR0 y < 2 ^ 32 ∧ (recipR0 y * (yw y 3 / 2 ^ 32) ≤ 2 ^ 63 ∧ 2 ^ 63 < recipR0 y * (yw y 3 / 2 ^ 32) + yw y 3 / 2 ^ 32 ∨
    (yw y 3 / 2 ^ 32 = 2 ^ 31 ∧ recipR0 y = 2 ^ 32 - 1)) := by
  have hyh : 2 ^ 31 ≤ yw y 3 / 2 ^ 32 ∧ yw y 3 / 2 ^ 32 < 2 ^ 32 := by numr; omega
  unfold recipR0
  by_cases hc : yw y 3 / 2 ^ 32 = 2 ^ 31
  · rw [if_pos hc]; exact ⟨by omega, Or.inr ⟨hc, rfl⟩⟩
  · rw [if_neg hc]
    generalize yw y 3 / 2 ^ 32 = yh at *
    have hpos : 0 < yh := by numr; omega
    have hdm := Nat.div_add_mod (2 ^ 63) yh
    have hlt := Nat.mod_lt (2 ^ 63) hpos
    generalize 2 ^ 63 / yh = q at *
    generalize 2 ^ 63 % yh = rr at *
    have e : yh * q = q * yh := Nat.mul_comm _ _
    refine ⟨?_, Or.inl ⟨by omega, by omega⟩⟩
    apply Nat.lt_of_not_ge; intro hq
    have := Nat.mul_le_mul_right yh hq
    numr
    omega

theorem div_mod192 (y : Nat) : y = y / 2 ^ 192 * 2 ^ 192 + y % 2 ^ 192 := by omega

/-- the signed stage-1 value `2 R0 - 2 t1` satisfies the Newton window -/
theorem stage1_int (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    -(2 ^ 260 : Int) ≤ 2 ^ 319 - (2 * ((recipR0 y : Int) * 2 ^ 32) - 2 * (recipT1 y : Int)) * y ∧
    2 ^ 319 - (2 * ((recipR0 y : Int) * 2 ^ 32) - 2 * (recipT1 y : Int)) * y ≤ 2 ^ 260 := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  have hy3 : 2 ^ 63 ≤ yw y 3 := by numr; omega
  have hyh : 2 ^ 31 ≤ yw y 3 / 2 ^ 32 ∧ yw y 3 / 2 ^ 32 < 2 ^ 32 := by numr; omega
  have hr0 := recipR0_facts y hy3 b3
  obtain ⟨hr0lt, hq⟩ := hr0
  have ht : 2 ^ 64 * recipT1 y ≤ recipR0 y * recipR0 y * yw y 3 ∧
      recipR0 y * recipR0 y * yw y 3 < 2 ^ 64 * recipT1 y + 2 ^ 64 := by
    unfold recipT1
    have hrr : recipR0 y * recipR0 y < 2 ^ 64 := by
      have := Nat.mul_lt_mul'' hr0lt hr0lt
      simpa [← Nat.pow_add] using this
    rw [Nat.mod_eq_of_lt hrr]
    have hdm := Nat.div_add_mod (recipR0 y * recipR0 y * yw y 3) (2 ^ 64)
    have hlt := Nat.mod_lt (recipR0 y * recipR0 y * yw y 3) (Nat.two_pow_pos 64)
    generalize recipR0 y * recipR0 y * yw y 3 / 2 ^ 64 = t at *
    generalize recipR0 y * recipR0 y * yw y 3 % 2 ^ 64 = rem at *
    omega
  have hyh' : yw y 3 / 2 ^ 32 = y / 2 ^ 224 := by omega
  have hyl : y = y / 2 ^ 224 * 2 ^ 224 + y % 2 ^ 224 := by omega
  have hyy : y = yw y 3 * 2 ^ 192 + y % 2 ^ 192 := by rw [h3]; exact div_mod192 y
  have hyl' := Nat.mod_lt y (Nat.two_pow_pos 224)
  have hyy' := Nat.mod_lt y (Nat.two_pow_pos 192)
  rw [hyh'] at hq hyh
  generalize recipR0 y = r0 at *
  generalize recipT1 y = t1 at *
  generalize yw y 3 = y3 at *
  generalize y / 2 ^ 224 = yh at *
  generalize y % 2 ^ 224 = yl at *
  generalize y % 2 ^ 192 = yy at *
  have hI : ((y : Nat) : Int) = (yh : Int) * 2 ^ 224 + yl := by exact_mod_cast hyl
  have hJ : ((y : Nat) : Int) = (y3 : Int) * 2 ^ 192 + yy := by exact_mod_cast hyy
  have hq' : ((r0 : Int) * yh ≤ 2 ^ 63 ∧ 2 ^ 63 < (r0 : Int) * yh + yh) ∨ ((yh : Int) = 2 ^ 31 ∧ (r0 : Int) = 2 ^ 32 - 1) := by
    rcases hq with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
    · right; refine ⟨by exact_mod_cast a, ?_⟩; rw [b]; omega
  have ht' : 2 ^ 64 * (t1 : Int) ≤ (r0 : Int) * r0 * y3 ∧ (r0 : Int) * r0 * y3 < 2 ^ 64 * t1 + 2 ^ 64 := by
    exact ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have hyI : (2 : Int) ^ 255 ≤ y ∧ (y : Int) < 2 ^ 256 := by constructor <;> omega
  have hD := d0win r0 yh yl y hI ⟨by omega, by exact_mod_cast hyl'⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hq'
  have hT := T1win r0 y3 yy y t1 hJ ⟨by omega, by exact_mod_cast hyy'⟩ ⟨by omega, by omega⟩ (by omega) ht'
  exact stage1 y (r0 * 2 ^ 32) _ (2 * t1) hyI rfl hT hD

theorem recipR0_val (y : Nat) (h : yw y 3 / 2 ^ 32 = 2 ^ 31) : recipR0 y = 2 ^ 32 - 1 := by
  unfold recipR0; rw [if_pos h]

theorem r1_spec (y : Nat) (hy1 : 2 ^ 255 < y) (hy2 : y < 2 ^ 256) :
    recipR1 y < 2 ^ 64 ∧ 2 ^ 319 ≤ recipR1 y * y + 2 ^ 260 ∧ recipR1 y * y ≤ 2 ^ 319 + 2 ^ 260 := by
  obtain ⟨hd, b0, b1, b2, b3, h3⟩ := yw_decomp y hy2
  have hy3 : 2 ^ 63 ≤ yw y 3 := by numr; omega
  have hlow := stage1_int y hy1 hy2
  have hr0 := recipR0_facts y hy3 b3
  by_cases hc : yw y 3 = 2 ^ 63
  · have hyh : yw y 3 / 2 ^ 32 = 2 ^ 31 := by rw [hc]
    have e0 := recipR0_val y hyh
    have e1 : recipT1 y = 2 ^ 63 - 2 ^ 32 := by unfold recipT1; rw [e0, hc]; try decide
    have e2 : recipR1raw y = 0 := by unfold recipR1raw; rw [e0, e1]; try decide
    have e3 : recipR1 y = 2 ^ 64 - 1 := by
      unfold recipR1; rw [e2, hc]; try rw [if_pos (by decide)]
    rw [e3]
    numr
    omega
  · have hy3' : 2 ^ 63 < yw y 3 := by omega
    have nz : 2 * yw y 3 % 2 ^ 64 ≠ 0 := by numr; omega
    have e3 : recipR1 y = recipR1raw y := by
      unfold recipR1
      rw [if_neg]
      intro h
      exact nz (Nat.or_eq_zero_iff.1 h).2
    have hr0lt := hr0.1
    have hlt : 2 ^ 32 * recipR0 y < 2 ^ 63 + recipT1 y := by
      have hrr : recipR0 y * recipR0 y < 2 ^ 64 := by
        have := Nat.mul_lt_mul'' hr0lt hr0lt
        simpa [← Nat.pow_add] using this
      have hT : recipT1 y = recipR0 y * recipR0 y * yw y 3 / 2 ^ 64 := by
        unfold recipT1; rw [Nat.mod_eq_of_lt hrr]
      rw [hT]
      by_cases hh : yw y 3 / 2 ^ 32 = 2 ^ 31
      · have e0 := recipR0_val y hh
        rw [e0]
        have := stage1_top (yw y 3) hy3' (by omega)
        numr
        omega
      · have hq : recipR0 y * (yw y 3 / 2 ^ 32) ≤ 2 ^ 63 := by
          rcases hr0.2 with ⟨a, _⟩ | ⟨a, _⟩
          · exact a
          · exact absurd a hh
        exact t1_big _ _ _ hq (by numr; omega) (by omega)
    have hlt' : recipT1 y < 2 ^ 63 + recipT1 y := by omega
    have hpos : 0 < 2 * ((recipR0 y : Int) * 2 ^ 32) - 2 * (recipT1 y : Int) := by
      apply Int.lt_of_not_ge; intro hn
      have hy0 : (0 : Int) ≤ y := Int.natCast_nonneg _
      have := Int.mul_le_mul_of_nonneg_right hn hy0
      have h0 : (0 : Int) * y = 0 := Int.zero_mul _
      have := hlow.2
      numr
      omega
    have hraw : recipR1raw y = 2 * (recipR0 y * 2 ^ 32 - recipT1 y) := by
      unfold recipR1raw
      omega
    have hr1 : (recipR1 y : Int) = 2 * ((recipR0 y : Int) * 2 ^ 32) - 2 * (recipT1 y : Int) := by
      rw [e3, hraw]
      omega
    rw [← hr1] at hlow
    have hlt64 : recipR1 y < 2 ^ 64 := by rw [e3, hraw]; omega
    refine ⟨hlt64, ?_, ?_⟩
    · have := hlow.2; have h2 : (2 : Int) ^ 319 ≤ (recipR1 y : Int) * y + 2 ^ 260 := by omega
      exact_mod_cast h2
    · have := hlow.1; have h2 : (recipR1 y : Int) * y ≤ 2 ^ 319 + 2 ^ 260 := by omega
      exact_mod_cast h2

end Fv256.F
