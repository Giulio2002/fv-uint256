/-!
# Integer square root by Newton iteration (math only, no machine code)

`Sqrt`: start with `z1 = 2^((bitlen x + 1)/2)` (so `x < (z1+1)^2`), repeat `z2 = (z1 + x / z1) / 2`; stop when `z2 ≥ z1` and return `z1`.
This file proves, over `Nat`, the facts the machine-code proofs need: the invariant `x < (z+1)^2` is preserved, a step with
`z*z > x` strictly decreases, and the first `z` with `z2 ≥ z` satisfies `z*z ≤ x < (z+1)*(z+1)`.
-/

namespace Fv256.SqrtMath

/-- `z` is the integer square root of `x` -/
def IsSqrt (x z : Nat) : Prop := z * z ≤ x ∧ x < (z + 1) * (z + 1)

theorem am_gm (a b : Nat) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.mul_add, Nat.add_mul]
    have := Nat.mul_comm a d
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.mul_add, Nat.add_mul]
    have := Nat.mul_comm b d
    omega

/-- one Newton step -/
def step (x z : Nat) : Nat := (z + x / z) / 2

/-- the invariant `x < (z+1)^2` is preserved by a step (AM-GM) -/
theorem inv_step (x z : Nat) (hz : 0 < z) (h : x < (z + 1) * (z + 1)) : x < (step x z + 1) * (step x z + 1) := by
  unfold step
  generalize hm : (z + x / z) / 2 = m
  have hq : x < z * (x / z + 1) := by
    have := Nat.div_add_mod x z
    have := Nat.mod_lt x hz
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hag := am_gm z (x / z + 1)
  have h2 : z + (x / z + 1) ≤ 2 * (m + 1) := by omega
  have h3 : (z + (x / z + 1)) * (z + (x / z + 1)) ≤ (2 * (m + 1)) * (2 * (m + 1)) := Nat.mul_le_mul h2 h2
  have h4 : (2 * (m + 1)) * (2 * (m + 1)) = 4 * ((m + 1) * (m + 1)) := Nat.mul_mul_mul_comm 2 (m + 1) 2 (m + 1)
  omega

/-- a step from a `z` that is too large (`x < z*z`) decreases -/
theorem step_lt (x z : Nat) (hz : 0 < z) (h : x < z * z) : step x z < z := by
  unfold step
  have hq : x / z < z := by
    rw [Nat.div_lt_iff_lt_mul hz]; exact h
  omega

/-- if the step does not decrease, then `z*z ≤ x` -/
theorem le_of_step_ge (x z : Nat) (hz : 0 < z) (h : z ≤ step x z) : z * z ≤ x := by
  rcases Nat.lt_or_ge x (z * z) with hc | hc
  · have := step_lt x z hz hc
    omega
  · exact hc

/-- stop condition: invariant and no decrease give the integer square root -/
theorem isSqrt_of_stop (x z : Nat) (hz : 0 < z) (hinv : x < (z + 1) * (z + 1)) (hstop : z ≤ step x z) : IsSqrt x z :=
  ⟨le_of_step_ge x z hz hstop, hinv⟩

/-- a step stays positive while the invariant holds and `0 < x` -/
theorem step_pos (x z : Nat) (hz : 0 < z) (hx : 0 < x) (h : x < (z + 1) * (z + 1)) : 0 < step x z := by
  unfold step
  have hq0 := Nat.zero_le (x / z)
  by_cases hq : x / z = 0
  · have : x < z := by
      rcases Nat.div_eq_zero_iff.mp hq with h0 | h0
      · omega
      · exact h0
    omega
  · omega

/-- initial value: `z = 2^((n+1)/2)` for `x < 2^n` gives the invariant -/
theorem inv_init (x n : Nat) (h : x < 2 ^ n) : x < (2 ^ ((n + 1) / 2) + 1) * (2 ^ ((n + 1) / 2) + 1) := by
  have h1 : 2 ^ n ≤ 2 ^ ((n + 1) / 2) * 2 ^ ((n + 1) / 2) := by
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ ((n + 1) / 2) * 2 ^ ((n + 1) / 2) ≤ (2 ^ ((n + 1) / 2) + 1) * (2 ^ ((n + 1) / 2) + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- under the invariant the quotient is at most `z + 2` -/
theorem quot_le (x z : Nat) (hz : 0 < z) (h : x < (z + 1) * (z + 1)) : x / z ≤ z + 2 := by
  have h1 := Nat.div_add_mod x z
  have h2 := Nat.mod_lt x hz
  -- x = z * q + r, r < z; suppose q ≥ z + 3, then x ≥ z * (z + 3) ≥ (z+1)*(z+1)
  rcases Nat.lt_or_ge (z + 2) (x / z) with hc | hc
  · have h3 : z * (z + 3) ≤ z * (x / z) := Nat.mul_le_mul_left z (by omega)
    have e1 : (z + 1) * (z + 1) = z * z + 2 * z + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    have e2 : z * (z + 3) = z * z + 3 * z := by simp only [Nat.mul_add]; omega
    omega
  · exact hc

/-- the addition `z + x / z` inside a step is at most `2 z + 2`, so it fits any width exceeding `2 z + 2` -/
theorem sum_le (x z : Nat) (hz : 0 < z) (h : x < (z + 1) * (z + 1)) : z + x / z ≤ 2 * z + 2 := by
  have := quot_le x z hz h
  omega

/-- 256-bit path: with `2^64 ≤ x < 2^256` the starting value is `≤ 2^128`, and the addition never reaches `2^256` -/
theorem no_overflow_256 (x z : Nat) (hz : 0 < z) (hzle : z ≤ 2 ^ 128) (h : x < (z + 1) * (z + 1)) :
    z + x / z < 2 ^ 256 := by
  have := sum_le x z hz h
  have : 2 * 2 ^ 128 + 2 < 2 ^ 256 := by decide
  omega

/-- uint64 path: the addition `z1 + x0 / z1` never reaches `2^64` when `z1 ≤ 2^32` -/
theorem no_overflow_64 (x z : Nat) (hz : 0 < z) (hzle : z ≤ 2 ^ 32) (h : x < (z + 1) * (z + 1)) :
    z + x / z < 2 ^ 64 := by
  have := sum_le x z hz h
  have : 2 * 2 ^ 32 + 2 < 2 ^ 64 := by decide
  omega

/-- the starting value for a number of bit length `n ≤ 256` is `≤ 2^128` (`n ≤ 64`: `≤ 2^32`) -/
theorem init_le_256 (n : Nat) (h : n ≤ 256) : 2 ^ ((n + 1) / 2) ≤ 2 ^ 128 :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem init_le_64 (n : Nat) (h : n ≤ 64) : 2 ^ ((n + 1) / 2) ≤ 2 ^ 32 :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- the starting value is positive -/
theorem init_pos (n : Nat) : 0 < 2 ^ ((n + 1) / 2) := Nat.two_pow_pos _

/-- the loop: strong induction on `z` (the measure; each non-stopping step has `step x z < z`) -/
theorem newton_ind {P : Nat → Prop} (x : Nat)
    (hstop : ∀ z, 0 < z → x < (z + 1) * (z + 1) → z ≤ step x z → P z)
    (hrec : ∀ z, 0 < z → x < (z + 1) * (z + 1) → step x z < z → 0 < step x z → P (step x z) → P z)
    (hx : 0 < x) : ∀ z, 0 < z → x < (z + 1) * (z + 1) → P z := by
  intro z
  induction z using Nat.strongRecOn with
  | _ z ih =>
    intro hz hinv
    rcases Nat.lt_or_ge (step x z) z with hlt | hge
    · have hp := step_pos x z hz hx hinv
      exact hrec z hz hinv hlt hp (ih _ hlt hp (inv_step x z hz hinv))
    · exact hstop z hz hinv hge

end Fv256.SqrtMath
