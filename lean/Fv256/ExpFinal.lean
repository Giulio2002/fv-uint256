import Fv256.ExpMath
import Janus
namespace Fv256.F

theorem stage_full (r b w t : Nat) (hr : r < W) (hb : b < W) (hw : w < 2 ^ t) :
    expIter t (r, b, w) = (r * b ^ w % W, b ^ (2 ^ t) % W, 0) := by
  rw [expIter_eq t r b w hr hb, Nat.mod_eq_of_lt hw, Nat.div_eq_of_lt hw]

theorem stage_meq (r b w t : Nat) (hr : r < W) (hb : b < W) (hw : w < 2 ^ t) :
    MEq (expIter t (r, b, w)).1 (r * b ^ w) ∧ MEq (expIter t (r, b, w)).2.1 (b ^ (2 ^ t)) ∧ (expIter t (r, b, w)).1 < W ∧ (expIter t (r, b, w)).2.1 < W := by
  rw [stage_full r b w t hr hb hw]
  exact ⟨meq_mod _, meq_mod _, Nat.mod_lt _ (Nat.two_pow_pos _), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem word_bound (n lo ej : Nat) (hej : ej < 2 ^ 64) (h : 2 ^ lo * ej < 2 ^ n) :
    ej < 2 ^ (min n (lo + 64) - min n lo) := by
  rcases Nat.lt_or_ge n lo with h1 | h1
  · have : 2 ^ n ≤ 2 ^ lo := Nat.pow_le_pow_right (by omega) (by omega)
    have hp : 0 < 2 ^ lo := Nat.two_pow_pos _
    have : ej = 0 := by
      rcases Nat.eq_zero_or_pos ej with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ lo) h0
        omega
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    simp [this]
  · rw [Nat.min_eq_right h1]
    rcases Nat.lt_or_ge n (lo + 64) with h2 | h2
    · rw [Nat.min_eq_left (by omega)]
      have e : 2 ^ n = 2 ^ lo * 2 ^ (n - lo) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e] at h
      exact Nat.lt_of_mul_lt_mul_left h
    · rw [Nat.min_eq_right h2]
      have : lo + 64 - lo = 64 := by omega
      rw [this]; exact hej

theorem pow_fix (n lo ej : Nat) (h : 2 ^ lo * ej < 2 ^ n) : 2 ^ min n lo * ej = 2 ^ lo * ej := by
  rcases Nat.lt_or_ge n lo with h1 | h1
  · have : 2 ^ n ≤ 2 ^ lo := Nat.pow_le_pow_right (by omega) (by omega)
    have hp : 0 < 2 ^ lo := Nat.two_pow_pos _
    have : ej = 0 := by
      rcases Nat.eq_zero_or_pos ej with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ lo) h0
        omega
    simp [this]
  · rw [Nat.min_eq_right h1]

/-- Four loops of `Exp`: with `e = e0 + 2^64 e1 + 2^128 e2 + 2^192 e3 < 2^n`, `n ≤ 256`,
the final accumulator is `b^e mod 2^256`. -/
theorem exp_total (b e0 e1 e2 e3 n : Nat) (hb : b < W) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (h3 : e3 < 2 ^ 64)
    (hn : n ≤ 256) (he : e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 < 2 ^ n) :
    let s1 := expIter (min n 64) (1, b, e0)
    let s2 := expIter (min n 128 - min n 64) (s1.1, s1.2.1, e1)
    let s3 := expIter (min n 192 - min n 128) (s2.1, s2.2.1, e2)
    let s4 := expIter (min n 256 - min n 192) (s3.1, s3.2.1, e3)
    MEq s4.1 (b ^ (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3)) := by
  intro s1 s2 s3 s4
  have hW : 1 < W := by decide
  have b1 : 2 ^ 64 * e1 < 2 ^ n := by omega
  have b2 : 2 ^ 128 * e2 < 2 ^ n := by omega
  have b3 : 2 ^ 192 * e3 < 2 ^ n := by omega
  have b0 : 2 ^ 0 * e0 < 2 ^ n := by simpa using (by omega : e0 < 2 ^ n)
  have w0 := word_bound n 0 e0 h0 b0
  have w1 := word_bound n 64 e1 h1 b1
  have w2 := word_bound n 128 e2 h2 b2
  have w3 := word_bound n 192 e3 h3 b3
  simp only [Nat.zero_add, Nat.min_zero, Nat.sub_zero] at w0
  simp only [Nat.reduceAdd] at w1 w2 w3
  have f1 := pow_fix n 64 e1 b1
  have f2 := pow_fix n 128 e2 b2
  have f3 := pow_fix n 192 e3 b3
  -- stage 1
  obtain ⟨r1, q1, lr1, lq1⟩ := stage_meq 1 b e0 (min n 64) (by decide) hb w0
  -- stage 2
  obtain ⟨r2, q2, lr2, lq2⟩ := stage_meq s1.1 s1.2.1 e1 _ lr1 lq1 w1
  obtain ⟨r3, q3, lr3, lq3⟩ := stage_meq s2.1 s2.2.1 e2 _ lr2 lq2 w2
  obtain ⟨r4, q4, lr4, lq4⟩ := stage_meq s3.1 s3.2.1 e3 _ lr3 lq3 w3
  -- bases: s_j.2.1 ≡ b ^ 2^(min n (64 j))
  have T1 : min n 64 + (min n 128 - min n 64) = min n 128 := by omega
  have T2 : min n 128 + (min n 192 - min n 128) = min n 192 := by omega
  have qq1 : MEq s2.2.1 (b ^ 2 ^ min n 128) := by
    have := (q2.trans (MEq.pow q1 _))
    rw [← Nat.pow_mul, ← Nat.pow_add, T1] at this
    exact this
  have qq2 : MEq s3.2.1 (b ^ 2 ^ min n 192) := by
    have := (q3.trans (MEq.pow qq1 _))
    rw [← Nat.pow_mul, ← Nat.pow_add, T2] at this
    exact this
  -- accumulators
  have rr1 : MEq s1.1 (b ^ e0) := by simpa using r1
  have rr2 : MEq s2.1 (b ^ (e0 + 2 ^ 64 * e1)) := by
    have := r2.trans (MEq.mul rr1 (MEq.pow q1 e1))
    rw [← Nat.pow_mul, f1, ← Nat.pow_add] at this
    exact this
  have rr3 : MEq s3.1 (b ^ (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2)) := by
    have := r3.trans (MEq.mul rr2 (MEq.pow qq1 e2))
    rw [← Nat.pow_mul, f2, ← Nat.pow_add] at this
    exact this
  have rr4 : MEq s4.1 (b ^ (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3)) := by
    have := r4.trans (MEq.mul rr3 (MEq.pow qq2 e3))
    rw [← Nat.pow_mul, f3, ← Nat.pow_add] at this
    exact this
  exact rr4
theorem even_exp_zero (b e : Nat) (hb : b % 2 = 0) (he : 256 ≤ e) : b ^ e % 2 ^ 256 = 0 := by
  have h2 : 2 ∣ b := Nat.dvd_of_mod_eq_zero hb
  have h1 : 2 ^ 256 ∣ b ^ 256 := (Nat.pow_dvd_pow_iff (by decide)).2 h2
  have h3 : b ^ 256 ∣ b ^ e := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
    exact ⟨b ^ d, by rw [Nat.pow_add]⟩
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 h3)

theorem split4 (M : Janus.Arm64.Memory) (a : Nat) :
    M.readLE a 32 = M.readLE a 8 + 256 ^ 8 * (M.readLE (a + 8) 8 + 256 ^ 8 * (M.readLE (a + 16) 8 + 256 ^ 8 * M.readLE (a + 24) 8)) := by
  rw [show (32:Nat) = 8 + 24 by rfl, Janus.Arm64.Memory.readLE_add, show (24:Nat) = 8 + 16 by rfl,
    Janus.Arm64.Memory.readLE_add (a := a + 8), show (16:Nat) = 8 + 8 by rfl, Janus.Arm64.Memory.readLE_add (a := a + 8 + 8)]

theorem exp_stage0 (b e0 n : Nat) (hb : b < W) (he : e0 < 2 ^ n) :
    (expIter n (1, b, e0)).1 = b ^ e0 % W := by
  rw [expIter_eq n 1 b e0 (by decide) hb, Nat.mod_eq_of_lt he, Nat.one_mul]

theorem copy32 (M : Janus.Arm64.Memory) (z p q1 q2 q3 : Nat) (h1 : q1 = p + 8) (h2 : q2 = p + 16) (h3 : q3 = p + 24)
    (d1 : z + 32 ≤ p ∨ p + 32 ≤ z) :
    ((((M.writeLE z 8 (M.readLE p 8)).writeLE (z + 8) 8 (M.readLE q1 8)).writeLE (z + 16) 8 (M.readLE q2 8)).writeLE (z + 24) 8 (M.readLE q3 8)).readLE z 32
      = M.readLE p 32 := by
  subst h1 h2 h3
  rw [split4 _ z, split4 M p]
  have l0 := Janus.Arm64.Memory.readLE_lt M p 8
  have l1 := Janus.Arm64.Memory.readLE_lt M (p + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt M (p + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt M (p + 24) 8
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    show z + 8 + 8 = z + 16 by omega, show z + 8 + 16 = z + 24 by omega, show z + 16 + 8 = z + 24 by omega]
  rw [Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2, Nat.mod_eq_of_lt l3]
end Fv256.F
