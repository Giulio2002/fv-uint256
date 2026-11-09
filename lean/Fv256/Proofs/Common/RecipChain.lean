import Fv256.Proofs.Common.RecipChain4

/-!
# `Reciprocal`: the master chain theorem (Extracted-free)

`recip_chain m`: for `2^192 ≤ m < 2^256` the pure-Nat model `recipModel m` satisfies `RecipWeak` and, for `m ≥ 2^193`, `RecipOK`
(`recip_lt192`: `recipModel m = 0` below `2^192`).  Covers the power-of-two branch, every shift `s ≤ 63`, and the `y3 = 2^63` edge.
-/

namespace Fv256.F
open Fv256.RecipMath
set_option exponentiation.threshold 1024

theorem pow2_div (n i : Nat) (h : i ≤ n) : (2 ^ n - 1) / 2 ^ i = 2 ^ (n - i) - 1 := by
  have e : 2 ^ i * 2 ^ (n - i) = 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  have ha := Nat.two_pow_pos i
  have hb := Nat.two_pow_pos (n - i)
  generalize 2 ^ i = a at *
  generalize 2 ^ (n - i) = b at *
  rw [← e]
  apply Nat.div_eq_of_lt_le
  · have : (b - 1) * a = a * b - a := by
      rw [Nat.mul_comm, Nat.mul_sub, Nat.mul_one]
    have h2 : a * b ≥ a := Nat.le_mul_of_pos_right a hb
    omega
  · have : b * a = a * b := Nat.mul_comm _ _
    have h2 : a * b ≥ a := Nat.le_mul_of_pos_right a hb
    have h3 : (b - 1 + 1) * a = b * a := by rw [Nat.sub_add_cancel hb]
    omega

/-- the power-of-two branch is exact -/
theorem recipPow2_ok (m : Nat) (h1 : 2 ^ 192 ≤ m) (h2 : m < 2 ^ 256) (hp : m = 2 ^ Nat.log2 m) :
    RecipOK m (recipPow2 m) := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos 192; omega
  have hL1 : 192 ≤ Nat.log2 m := (Nat.le_log2 hm0).2 h1
  have hL2 : Nat.log2 m < 256 := (Nat.log2_lt hm0).2 h2
  generalize hL : Nat.log2 m = L at *
  have hmod : L % 64 = L - 192 := by omega
  unfold RecipOK recipExact recipPow2
  rw [hL, hmod]
  rw [hp, pow2_mu L (by omega), pow2_div 64 (L - 192) (by omega)]
  have e : 2 ^ 256 * 2 ^ (64 - (L - 192)) = 2 ^ (512 - L) := by
    rw [← Nat.pow_add, show 256 + (64 - (L - 192)) = 512 - L by omega]
  have hb := Nat.two_pow_pos (64 - (L - 192))
  have hc := Nat.two_pow_pos 256
  have hd := Nat.two_pow_pos (512 - L)
  have e2 : 2 ^ 256 * (2 ^ (64 - (L - 192)) - 1) = 2 ^ 256 * 2 ^ (64 - (L - 192)) - 2 ^ 256 := by
    rw [Nat.mul_sub, Nat.mul_one]
  have h3 : 2 ^ 256 * 2 ^ (64 - (L - 192)) ≥ 2 ^ 256 := Nat.le_mul_of_pos_right _ hb
  generalize 2 ^ 256 * 2 ^ (64 - (L - 192)) = P at *
  generalize 2 ^ 256 = Q at *
  generalize 2 ^ (512 - L) = T at *
  constructor <;> omega

theorem recip_chain (m : Nat) (h1 : 2 ^ 192 ≤ m) (h2 : m < 2 ^ 256) :
    RecipWeak m (recipModel m) ∧ (2 ^ 193 ≤ m → RecipOK m (recipModel m)) := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos 192; omega
  have hn : ¬ m < 2 ^ 192 := by omega
  unfold recipModel
  rw [if_neg hn]
  by_cases hp : m = 2 ^ Nat.log2 m
  · rw [if_pos hp]
    have := recipPow2_ok m h1 h2 hp
    exact ⟨this.weak, fun _ => this⟩
  · rw [if_neg hp]
    have hL1 : 192 ≤ Nat.log2 m := (Nat.le_log2 hm0).2 h1
    have hL2 : Nat.log2 m < 256 := (Nat.log2_lt hm0).2 h2
    have hlo : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le hm0
    have hhi : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
    have hlo' : 2 ^ Nat.log2 m < m := by omega
    have hnp : ∀ i, m ≠ 2 ^ i := by
      intro i hi
      apply hp
      rw [hi, Nat.log2_two_pow]
    have hs : recipS m ≤ 63 := by unfold recipS; omega
    have hy1 : 2 ^ 255 < recipY m := by
      unfold recipY recipS
      have e : 2 ^ 255 = 2 ^ Nat.log2 m * 2 ^ (255 - Nat.log2 m) := by rw [← Nat.pow_add, show Nat.log2 m + (255 - Nat.log2 m) = 255 by omega]
      rw [e]
      exact Nat.mul_lt_mul_of_pos_right hlo' (Nat.two_pow_pos _)
    have hy2 : recipY m < 2 ^ 256 := by
      unfold recipY recipS
      have e : 2 ^ 256 = 2 ^ (Nat.log2 m + 1) * 2 ^ (255 - Nat.log2 m) := by rw [← Nat.pow_add, show Nat.log2 m + 1 + (255 - Nat.log2 m) = 256 by omega]
      rw [e]
      exact Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
    obtain ⟨ra, rb, rc⟩ := r4_spec (recipY m) hy1 hy2
    have hm : 2 ^ (255 - recipS m) ≤ m ∧ m < 2 ^ (256 - recipS m) := by
      have e1 : 255 - recipS m = Nat.log2 m := by unfold recipS; omega
      have e2 : 256 - recipS m = Nat.log2 m + 1 := by unfold recipS; omega
      rw [e1, e2]; exact ⟨hlo, hhi⟩
    have hmu := mu_window m (recipS m) (recipR4 (recipY m)) (recipTail (recipS m) (recipR4 (recipY m))) hs hm hnp
      ⟨ra, rb⟩ (fun h => by unfold recipTail; rw [if_pos h]) (fun h => by
        unfold recipTail
        rw [if_neg (by omega)]
        exact Nat.mod_eq_of_lt (by omega))
    refine ⟨hmu.1, fun h193 => hmu.2 ?_⟩
    have : 193 ≤ Nat.log2 m := (Nat.le_log2 hm0).2 h193
    unfold recipS; omega

end Fv256.F
