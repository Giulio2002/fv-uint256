/-!
# `func (z *Int) Log10() uint`

`z.Log10()` returns the number of decimal digits of `z` minus one, i.e. `⌊log₁₀ z⌋` for `z > 0` (so `0..77`), and `0` for `z = 0`.
It has no error or panic case. Specified as a relation: `r` is the answer when `10^r <= z < 10^(r+1)` (the unique such `r`).
-/

namespace Fv256.Spec

/-- `r` is a correct result of `z.Log10()` for `z = x`: `0` when `x = 0`, otherwise `r` is the exponent with `10^r <= x < 10^(r+1)`. -/
def IsLog10 (x r : Nat) : Prop := (x = 0 → r = 0) ∧ (x ≠ 0 → 10 ^ r ≤ x ∧ x < 10 ^ (r + 1))

/-- The relation is decidable (for the `example` checks below). -/
instance (x r : Nat) : Decidable (IsLog10 x r) :=
  inferInstanceAs (Decidable ((x = 0 → r = 0) ∧ (x ≠ 0 → 10 ^ r ≤ x ∧ x < 10 ^ (r + 1))))

example : IsLog10 0 0 := by decide
example : IsLog10 9 0 := by decide
example : IsLog10 10 1 := by decide
example : IsLog10 12345 4 := by decide

/-- A wrong answer is rejected. -/
example : ¬ IsLog10 12345 5 := by decide

end Fv256.Spec
