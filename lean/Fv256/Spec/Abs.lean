/-!
# `func (z *Int) Abs(x *Int) *Int`

`z.Abs(x)` reads `x` as a two's-complement signed number and sets `z` to its absolute value, returning `z`. A number below `2^255` is non-negative and unchanged; any other number is negative and is replaced by `2^256 - x`. The most negative number `2^255` is its own absolute value (it has no positive counterpart). No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Abs(x)`: `x` itself when its top bit is clear, otherwise the two's-complement negation `2^256 - x`. -/
def abs (x : Nat) : Nat := if x < 2 ^ 255 then x else (2 ^ 256 - x) % 2 ^ 256

/-- Non-negative numbers are unchanged. -/
example : abs 5 = 5 := by decide

/-- Minus one has absolute value one. -/
example : abs (2 ^ 256 - 1) = 1 := by decide

/-- The most negative number maps to itself. -/
example : abs (2 ^ 255) = 2 ^ 255 := by decide

end Fv256.Spec
