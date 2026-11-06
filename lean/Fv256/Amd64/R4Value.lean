import Fv256.MulModMath
import Fv256.MulModTrunc

/-! `reduce4` (amd64): the pure value lemma assembling the arithmetic facts into `dsum % m = x % m`. -/

set_option exponentiation.threshold 700
namespace Fv256.Amd64.R4Seg

open Fv256.F

theorem r4_value (X0 X1 X2 X3 X4 X5 X6 X7 U0 U1 U2 U3 U4 M0 M1 M2 M3 q B R1 r9 dsum : Nat)
    (bX0 : X0 < 2 ^ 64) (bX1 : X1 < 2 ^ 64) (bX2 : X2 < 2 ^ 64) (bX3 : X3 < 2 ^ 64) (bX4 : X4 < 2 ^ 64)
    (bX5 : X5 < 2 ^ 64) (bX6 : X6 < 2 ^ 64) (bX7 : X7 < 2 ^ 64)
    (bU0 : U0 < 2 ^ 64) (bU1 : U1 < 2 ^ 64) (bU2 : U2 < 2 ^ 64) (bU3 : U3 < 2 ^ 64) (bU4 : U4 < 2 ^ 64)
    (bM0 : M0 < 2 ^ 64) (bM1 : M1 < 2 ^ 64) (bM2 : M2 < 2 ^ 64) (bM3 : M3 < 2 ^ 64) (hM3 : 1 ≤ M3)
    (hRW : RecipWeak (M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3) (U0 + 2 ^ 64 * U1 + 2 ^ 128 * U2 + 2 ^ 192 * U3 + 2 ^ 256 * U4))
    (h1 : q * 2 ^ 320 ≤ (X3 + 2 ^ 64 * X4 + 2 ^ 128 * X5 + 2 ^ 192 * X6 + 2 ^ 256 * X7) * (U0 + 2 ^ 64 * U1 + 2 ^ 128 * U2 + 2 ^ 192 * U3 + 2 ^ 256 * U4))
    (h2 : (X3 + 2 ^ 64 * X4 + 2 ^ 128 * X5 + 2 ^ 192 * X6 + 2 ^ 256 * X7) * (U0 + 2 ^ 64 * U1 + 2 ^ 128 * U2 + 2 ^ 192 * U3 + 2 ^ 256 * U4) < q * 2 ^ 320 + 2 * 2 ^ 320)
    (hB : B = (q * (M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3)) % 2 ^ 320)
    (hR1 : R1 = (X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 + 2 ^ 320 - B) % 2 ^ 320)
    (hmask : r9 = 0 ↔ B ≤ X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4)
    (hd : dsum = (R1 + (if r9 = 0 then 0 else M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3)) % 2 ^ 320) :
    dsum % (M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3) =
      (X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 + 2 ^ 320 * X5 + 2 ^ 384 * X6 + 2 ^ 448 * X7) % (M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3) := by
  generalize hm : M0 + 2 ^ 64 * M1 + 2 ^ 128 * M2 + 2 ^ 192 * M3 = m at *
  generalize hx : X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 + 2 ^ 320 * X5 + 2 ^ 384 * X6 + 2 ^ 448 * X7 = x
  generalize hmu : U0 + 2 ^ 64 * U1 + 2 ^ 128 * U2 + 2 ^ 192 * U3 + 2 ^ 256 * U4 = mu at *
  have hx512 : x < 2 ^ 512 := by omega
  have hm1 : 2 ^ 192 ≤ m := by omega
  have hm2 : m < 2 ^ 256 := by omega
  have hq1' : x / 2 ^ 192 = X3 + 2 ^ 64 * X4 + 2 ^ 128 * X5 + 2 ^ 192 * X6 + 2 ^ 256 * X7 := by omega
  have hq : x / 2 ^ 192 * mu / 2 ^ 320 ≤ q + 1 ∧ q ≤ x / 2 ^ 192 * mu / 2 ^ 320 := by
    rw [hq1']
    constructor
    · rw [Nat.div_le_iff_le_mul_add_pred (by decide)]
      omega
    · rw [Nat.le_div_iff_mul_le (by decide)]
      omega
  obtain ⟨hlt, hmod⟩ := reduce_value x m mu q hx512 hm1 hm2 hRW hq.1 hq.2
  have ha : x % 2 ^ 320 = X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 := by omega
  unfold reduceR at hlt hmod
  simp only [] at hlt hmod
  rw [← hB, ha, ← hR1] at hlt hmod
  by_cases hc : r9 = 0
  · have hba := hmask.mp hc
    have hnl : ¬ (X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 < B) := by omega
    rw [if_neg hnl] at hlt hmod
    rw [hd, if_pos hc]
    have : (R1 + 0) % 2 ^ 320 = R1 := by omega
    rw [this]; exact hmod
  · have hab : ¬ B ≤ X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 := fun h => hc (hmask.mpr h)
    have hl : X0 + 2 ^ 64 * X1 + 2 ^ 128 * X2 + 2 ^ 192 * X3 + 2 ^ 256 * X4 < B := by omega
    rw [if_pos hl] at hlt hmod
    rw [hd, if_neg hc]
    have : (R1 + m) % 2 ^ 320 = R1 + m := Nat.mod_eq_of_lt hlt
    rw [this]; exact hmod

end Fv256.Amd64.R4Seg
