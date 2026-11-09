/-!
# `func (z *Int) Sqrt(x *Int) *Int`

`z.Sqrt(x)` sets `z` to the integer square root of `x`: the largest `r` with `r * r ≤ x` (the square root rounded down), and returns `z`.
It is exact on perfect squares, `Sqrt(0) = 0`, and has no error or panic case. The specification below states this as a property
that pins `z` down uniquely, so it is checked on the whole range `0 ≤ x < 2^256` without any algorithm being fixed.
-/

namespace Fv256.Spec

/-- `z` is the integer square root of `x`, i.e. `z = ⌊√x⌋`: the square of `z` does not exceed `x`, and the square of `z + 1` does.
Exactly one `z` satisfies this for each `x`. -/
def IsSqrt (x z : Nat) : Prop := z * z ≤ x ∧ x < (z + 1) * (z + 1)

/-- The square root of a perfect square is its root. -/
example : IsSqrt 49 7 := by decide

/-- Rounding down: `⌊√50⌋ = 7`. -/
example : IsSqrt 50 7 := by decide

/-- `⌊√0⌋ = 0`. -/
example : IsSqrt 0 0 := by decide

/-- The largest word has the 128-bit root `2^128 - 1`. -/
example : IsSqrt (2 ^ 256 - 1) (2 ^ 128 - 1) := by decide

end Fv256.Spec
