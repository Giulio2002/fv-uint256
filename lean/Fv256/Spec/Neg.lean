/-!
# `func (z *Int) Neg(x *Int) *Int`

`z.Neg(x)` sets `z = -x` in two's complement, i.e. `2^256 - x` modulo `2^256`, and returns `z`. Negating zero gives zero. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Neg(x)`: the two's-complement negation of the 256-bit number `x` (`0` for `0`, otherwise `2^256 - x`). -/
def neg (x : Nat) : Nat := (2 ^ 256 - x) % 2 ^ 256

/-- Zero is its own negation. -/
example : neg 0 = 0 := by decide

/-- Negating one gives the largest word. -/
example : neg 1 = 2 ^ 256 - 1 := by decide

/-- The most negative number is its own negation. -/
example : neg (2 ^ 255) = 2 ^ 255 := by decide

end Fv256.Spec
