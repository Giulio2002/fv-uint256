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

end Fv256.SqrtMath
