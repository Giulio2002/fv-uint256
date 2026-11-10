import Fv256.Spec.Div
import Fv256.Spec.Mod

/-!
# `func (z *Int) DivMod(x, y, m *Int) (*Int, *Int)`

`z.DivMod(x, y, m)` sets `z = x / y` (rounded down) and `m = x mod y`, and returns the pair `(z, m)`.
Division by zero is NOT an error and does not panic: both results are `0`.
When `z` and `m` are the same object the Go code works on a fresh copy of `m`, so the second returned pointer is then a new
object that holds the remainder; the number values are the same.

There is nothing new to define: the quotient is exactly `Fv256.Spec.div x y` (`Spec/Div.lean`) and the remainder exactly
`Fv256.Spec.mod x y` (`Spec/Mod.lean`), computed from the same inputs `x`, `y`. The machine claims state both.
-/

namespace Fv256.Spec

/-- `7 = 2 * 3 + 1`: quotient and remainder. -/
example : div 7 2 = 3 ∧ mod 7 2 = 1 := by decide

/-- Division by zero gives `(0, 0)`. -/
example : div 7 0 = 0 ∧ mod 7 0 = 0 := by decide

/-- The two results recombine: `x = q * y + r` for `y ≠ 0` (checked on one case). -/
example : div 100 7 * 7 + mod 100 7 = 100 := by decide

end Fv256.Spec
