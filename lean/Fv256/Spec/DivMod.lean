import Fv256.Spec.Div
import Fv256.Spec.Mod

/-!
# `func (z *Int) DivMod(x, y, m *Int) (*Int, *Int)`

`z.DivMod(x, y, m)` sets `z = x / y` (rounded down) and `m = x mod y`, and returns the pair `(z, m)`.
Division by zero is NOT an error and does not panic: both results are `0`.
When `z` and `m` are the same object the Go code works on a fresh copy of `m`, so the second returned pointer is then a new
object that holds the remainder; the number values are the same.
-/

namespace Fv256.Spec

/-- Value of `z.DivMod(x, y, m)`: the pair (quotient `Spec.div x y`, remainder `Spec.mod x y`), both `0` when `y = 0`. -/
def divMod (x y : Nat) : Nat × Nat := (div x y, mod x y)

/-- `7 = 2 * 3 + 1`. -/
example : divMod 7 2 = (3, 1) := by decide

/-- Division by zero gives `(0, 0)`. -/
example : divMod 7 0 = (0, 0) := by decide

/-- The two results recombine: `x = q * y + r` for `y ≠ 0` (checked on one case). -/
example : (divMod 100 7).1 * 7 + (divMod 100 7).2 = 100 := by decide

end Fv256.Spec
