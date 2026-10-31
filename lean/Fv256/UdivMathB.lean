import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

namespace Fv256.B

theorem shl_word (m s : Nat) (hs : s < 64) :
    m * 2 ^ s = 2 ^ 64 * (m / 2 ^ (64 - s)) + (m * 2 ^ s) % 2 ^ 64 := by
  have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : m * 2 ^ s / 2 ^ 64 = m / 2 ^ (64 - s) := by
    rw [e64, Nat.mul_comm m, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos s)]
  have := Nat.div_add_mod (m * 2 ^ s) (2 ^ 64)
  rw [h1] at this
  exact this.symm

/-- carry into word `k` of a left shift by `s`: the shifted-out part of word `k-1`. -/
def shc (M : Janus.Arm64.Memory) (p s k : Nat) : Nat :=
  if k = 0 then 0 else M.readLE (p + 8 * (k - 1)) 8 / 2 ^ (64 - s)

/-- Shifting a word vector left by `s < 64` bits. -/
theorem shl_vec (M N : Janus.Arm64.Memory) (p q s K : Nat) (hs : s < 64)
    (hi : ∀ i, i < K → N.readLE (q + 8 * i) 8 = (M.readLE (p + 8 * i) 8 * 2 ^ s) % 2 ^ 64 + shc M p s i) :
    ∀ k, k ≤ K → wv N q k + shc M p s k * 2 ^ (64 * k) = wv M p k * 2 ^ s := by
  intro k
  induction k with
  | zero => intro _; simp [wv, shc]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have h1 := hi k (by omega)
    have hw := shl_word (M.readLE (p + 8 * k) 8) s hs
    have e2 : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
    have hc : shc M p s (k + 1) = M.readLE (p + 8 * k) 8 / 2 ^ (64 - s) := by simp [shc]
    rw [wv_snoc, wv_snoc, hc, e2, h1]
    generalize 2 ^ (64 * k) = T at *
    generalize shc M p s k = c at *
    generalize wv N q k = a at *
    generalize wv M p k = b at *
    generalize M.readLE (p + 8 * k) 8 / 2 ^ (64 - s) = qq at *
    generalize (M.readLE (p + 8 * k) 8 * 2 ^ s) % 2 ^ 64 = r at *
    generalize M.readLE (p + 8 * k) 8 = x at *
    grind

theorem shr_aux (x s : Nat) (hs : s < 64) :
    x / 2 ^ s * 2 ^ 64 + (x % 2 ^ 64 * 2 ^ (64 - s)) % 2 ^ 64 = x * 2 ^ (64 - s) := by
  have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have hdm := Nat.div_add_mod x (2 ^ s)
  have hlt : x % 2 ^ s * 2 ^ (64 - s) < 2 ^ 64 := by
    rw [e64]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos s)) (Nat.two_pow_pos _)
  have h1 : x * 2 ^ (64 - s) = 2 ^ 64 * (x / 2 ^ s) + x % 2 ^ s * 2 ^ (64 - s) := by
    generalize x / 2 ^ s = a at hdm
    generalize x % 2 ^ s = b at hdm
    rw [← hdm, Nat.add_mul, e64]; grind
  have h2 : (x % 2 ^ 64 * 2 ^ (64 - s)) % 2 ^ 64 = (x * 2 ^ (64 - s)) % 2 ^ 64 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h2, h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  grind

/-- Shifting a word vector right by `s < 64` bits (the top word only gets its own shifted-down part). -/
theorem shr_vec (M N : Janus.Arm64.Memory) (s : Nat) (hs : s < 64) :
    ∀ K p q, (∀ i, i < K → N.readLE (q + 8 * i) 8 =
      M.readLE (p + 8 * i) 8 / 2 ^ s + (if i + 1 < K then (M.readLE (p + 8 * (i + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64 else 0)) →
      wv N q K = wv M p K / 2 ^ s := by
  intro K
  induction K with
  | zero => intro p q _; simp [wv]
  | succ K ih =>
    intro p q hi
    have h0 := hi 0 (by omega)
    have ih' := ih (p + 8) (q + 8) (fun i hi' => by
      have := hi (i + 1) (by omega)
      rw [show q + 8 * (i + 1) = q + 8 + 8 * i by omega, show p + 8 * (i + 1) = p + 8 + 8 * i by omega] at this
      rw [this]
      by_cases h : i + 1 < K
      · rw [if_pos h, if_pos (by omega)]
        rw [show p + 8 * (i + 1 + 1) = p + 8 + 8 * (i + 1) by omega]
      · rw [if_neg h, if_neg (by omega)])
    rw [wv_succ, wv_succ, ih']
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp [wv] at h0 ⊢
      exact h0
    · have hx : wv M (p + 8) K % 2 ^ 64 = M.readLE (p + 8 * (0 + 1)) 8 := by
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        rw [wv_succ]
        have := Janus.Arm64.Memory.readLE_lt M (p + 8) 8
        simp only [Nat.reducePow] at this ⊢
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt this]
      rw [if_pos (by omega)] at h0
      have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
      have haux := shr_aux (wv M (p + 8) K) s hs
      rw [hx] at haux
      have hdiv : (M.readLE p 8 + 2 ^ 64 * wv M (p + 8) K) / 2 ^ s = M.readLE p 8 / 2 ^ s + 2 ^ (64 - s) * wv M (p + 8) K := by
        rw [e64, Nat.mul_assoc, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos s)]
        omega
      rw [hdiv, h0]
      generalize wv M (p + 8) K = x at *
      generalize M.readLE (p + 8 * (0 + 1)) 8 = y at *
      rw [Nat.mul_comm (2 ^ (64 - s)) x]
      grind

theorem funnel_mach (a b s : Nat) (hs1 : 1 ≤ s) (hs : s ≤ 63) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 b >>> ((18446744073709551616 - s) % 64) &&& (if 63 - s + 1 < 64 then 18446744073709551615#64 else 0#64)) |||
      (BitVec.ofNat 64 a <<< ((18446744073709551616 - (64 - s)) % 64) &&& (if s < 64 then 18446744073709551615#64 else 0#64))).toNat =
      a * 2 ^ s % 2 ^ 64 + b / 2 ^ (64 - s) := by
  have c1 : (18446744073709551616 - s) % 64 = 64 - s := by omega
  have c2 : (18446744073709551616 - (64 - s)) % 64 = s := by omega
  have m1 : 63 - s + 1 < 64 := by omega
  have m2 : s < 64 := by omega
  rw [c1, c2, if_pos m1, if_pos m2, and_mask, and_mask]
  have := shld_toNat b a s hs1 (by omega) hb ha
  exact this

theorem shl_carry_lt (a b s : Nat) (hs : s < 64) (hb : b < 2 ^ 64) :
    a * 2 ^ s % 2 ^ 64 + b / 2 ^ (64 - s) < 2 ^ 64 := by
  have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : a * 2 ^ s % 2 ^ 64 = 2 ^ s * (a % 2 ^ (64 - s)) := by
    rw [e64, Nat.mul_comm a, Nat.mul_mod_mul_left]
  have h2 : a % 2 ^ (64 - s) < 2 ^ (64 - s) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : b / 2 ^ (64 - s) < 2 ^ s := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← e64]; exact hb
  rw [h1]
  have h4 : a % 2 ^ (64 - s) + 1 ≤ 2 ^ (64 - s) := h2
  have h5 := Nat.mul_le_mul_left (2 ^ s) h4
  rw [Nat.mul_add, ← e64] at h5
  omega

theorem funnel_mach' (a b s : Nat) (hs1 : 1 ≤ s) (hs : s ≤ 63) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 b >>> ((18446744073709551616 - s) % 64) &&& 18446744073709551615#64) |||
      (BitVec.ofNat 64 a <<< ((18446744073709551616 - (64 - s)) % 64) &&& 18446744073709551615#64)).toNat =
      a * 2 ^ s % 2 ^ 64 + b / 2 ^ (64 - s) := by
  have := funnel_mach a b s hs1 hs ha hb
  have m1 : 63 - s + 1 < 64 := by omega
  have m2 : s < 64 := by omega
  rw [if_pos m1, if_pos m2] at this
  exact this

end Fv256.B
