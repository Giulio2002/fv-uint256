import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Janus

/-!
# Pure-`Nat` facts for the arm64 `Reciprocal` proof: normalisation (`clz`) and the word form of a left shift
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Fv256.Arm64.RecipNat

open Janus.Arm64 in
theorem clz_norm : ∀ (n x : Nat), x < 2 ^ n → x ≠ 0 →
    2 ^ (n - 1) ≤ x * 2 ^ (clzNat n x) ∧ x * 2 ^ (clzNat n x) < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x hx h0; omega
  | succ n ih =>
    intro x hx h0
    have hc : clzNat (n + 1) x = if x.testBit n = true then 0 else 1 + clzNat n x := rfl
    rw [hc]
    by_cases hb : x.testBit n = true
    · rw [if_pos hb, Nat.pow_zero, Nat.mul_one]
      have h2 : 2 ^ n ≤ x := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · have := Nat.testBit_lt_two_pow hlt (i := n)
          rw [this] at hb
          exact absurd hb (by decide)
        · exact hge
      rw [Nat.add_sub_cancel]
      omega
    · rw [if_neg hb]
      have hxn : x < 2 ^ n := by
        rcases Nat.lt_or_ge x (2 ^ n) with hlt | hge
        · exact hlt
        · exfalso
          have h1 : x / 2 ^ n = 1 := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
              omega
          apply hb
          rw [Nat.testBit_eq_decide_div_mod_eq, h1]
          decide
      obtain ⟨h1, h2⟩ := ih x hxn h0
      have e : 2 ^ (1 + clzNat n x) = 2 * 2 ^ clzNat n x := by
        rw [Nat.add_comm, Nat.pow_succ]; omega
      rw [e]
      have e2 : x * (2 * 2 ^ clzNat n x) = 2 * (x * 2 ^ clzNat n x) := by
        rw [Nat.mul_left_comm]
      rw [e2]
      cases n with
      | zero => omega
      | succ k =>
        rw [Nat.add_sub_cancel]
        rw [Nat.add_sub_cancel] at h1
        have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
        have h4 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
        omega


theorem clz_le (x : Nat) (hx : x < 2 ^ 64) (h0 : x ≠ 0) : Janus.Arm64.clzNat 64 x ≤ 63 := by
  obtain ⟨_, h2⟩ := clz_norm 64 x hx h0
  by_cases hh : Janus.Arm64.clzNat 64 x ≤ 63
  · exact hh
  · exfalso
    have : 2 ^ 64 ≤ 2 ^ (Janus.Arm64.clzNat 64 x) := Nat.pow_le_pow_right (by omega) (by omega)
    have : 2 ^ (Janus.Arm64.clzNat 64 x) ≤ x * 2 ^ (Janus.Arm64.clzNat 64 x) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem top_ge (x0 x1 x2 x3 n : Nat) (hx0 : x0 < 2 ^ 64) (hx1 : x1 < 2 ^ 64) (hx2 : x2 < 2 ^ 64) (hx3 : x3 < 2 ^ 64)
    (h0 : x3 ≠ 0) (hn : n = Janus.Arm64.clzNat 64 x3) (v0 v1 v2 v3 : Nat) (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64)
    (hv2 : v2 < 2 ^ 64) (hv3 : v3 < 2 ^ 64)
    (hv : v0 + 2 ^ 64 * v1 + 2 ^ 128 * v2 + 2 ^ 192 * v3 =
      Fv256.Spec.lsh (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) n) : 2 ^ 63 ≤ v3 := by
  obtain ⟨hn1, hn2⟩ := clz_norm 64 x3 hx3 h0
  rw [← hn] at hn1 hn2
  unfold Fv256.Spec.lsh Fv256.Spec.W at hv
  simp only [Nat.reducePow, Nat.add_sub_cancel] at hn1 hn2 hv
  have hxs : x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 < 2 ^ 192 := by
    have : 2 ^ 64 * x1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ 128 * x2 ≤ 2 ^ 128 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- P = 2^n divides 2^64
  have hPpos := Nat.two_pow_pos n
  have hn64 : n < 64 := by
    by_cases hh : n < 64
    · exact hh
    · exfalso
      have : 2 ^ 64 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ n ≤ x3 * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
      omega
  have hPd : 2 ^ n * 2 ^ (64 - n) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  generalize 2 ^ n = P at *
  generalize 2 ^ (64 - n) = Q at *
  -- x3 < Q
  have hxQ : x3 < Q := by
    have : x3 * P < Q * P := by rw [Nat.mul_comm Q P, hPd]; exact hn2
    exact Nat.lt_of_mul_lt_mul_right this
  have hxQ1 : (x3 + 1) * P ≤ 2 ^ 64 := by
    rw [← hPd, Nat.mul_comm P Q]
    exact Nat.mul_le_mul_right P hxQ
  have e1 : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * P = (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P + 2 ^ 192 * (x3 * P) := by
    grind
  have hRP : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P < 2 ^ 192 * P := Nat.mul_lt_mul_of_pos_right hxs hPpos
  have hlt : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * P < 2 ^ 256 := by
    rw [e1]
    have : 2 ^ 192 * (x3 * P) + 2 ^ 192 * P ≤ 2 ^ 192 * 2 ^ 64 := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      have : (x3 + 1) * P = x3 * P + P := by grind
      omega
    omega
  rw [Nat.mod_eq_of_lt hlt, e1] at hv
  generalize (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2) * P = RP at *
  generalize x3 * P = XP at *
  have hv0' := hv0
  omega

set_option maxRecDepth 100000 in
theorem word_or (a b n : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    (b * 2 ^ n % 2 ^ 64 ||| (BitVec.ofNat 64 a >>> ((18446744073709551616 - n - 18446744073709551552) % 64)).toNat) =
      b * 2 ^ n % 2 ^ 64 + a / 2 ^ (64 - n) := by
  have e1 : 18446744073709551616 - n - 18446744073709551552 = 64 - n := by
    rw [Nat.sub_right_comm]
  have e : (18446744073709551616 - n - 18446744073709551552) % 64 = 64 - n := by rw [e1]; exact Nat.mod_eq_of_lt (by omega)
  rw [e, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha]
  have hp : 2 ^ 64 = 2 ^ n * 2 ^ (64 - n) := by rw [← Nat.pow_add, show n + (64 - n) = 64 by omega]
  have hp' : 2 ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [Nat.mul_comm]; exact hp
  have hq : a / 2 ^ (64 - n) < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; rw [← hp]; exact ha
  have hm : b * 2 ^ n % 2 ^ 64 = (b % 2 ^ (64 - n)) * 2 ^ n := by
    rw [hp']; exact Nat.mul_mod_mul_right (2 ^ n) b (2 ^ (64 - n))
  rw [hm, Nat.or_comm, Util.or_hi _ _ n hq, Nat.add_comm]
set_option maxRecDepth 100000 in
theorem word_lt (a b n : Nat) (ha : a < 2 ^ 64) (h2 : n ≤ 63) :
    b * 2 ^ n % 2 ^ 64 + a / 2 ^ (64 - n) < 2 ^ 64 := by
  have hp : 2 ^ 64 = 2 ^ n * 2 ^ (64 - n) := by rw [← Nat.pow_add, show n + (64 - n) = 64 by omega]
  have hp' : 2 ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [Nat.mul_comm]; exact hp
  have hq : a / 2 ^ (64 - n) < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; rw [← hp]; exact ha
  have hm : b * 2 ^ n % 2 ^ 64 = (b % 2 ^ (64 - n)) * 2 ^ n := by
    rw [hp']; exact Nat.mul_mod_mul_right (2 ^ n) b (2 ^ (64 - n))
  rw [hm]
  have h1 : b % 2 ^ (64 - n) + 1 ≤ 2 ^ (64 - n) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : (b % 2 ^ (64 - n) + 1) * 2 ^ n ≤ 2 ^ (64 - n) * 2 ^ n := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, ← hp'] at h3
  omega
end Fv256.Arm64.RecipNat
