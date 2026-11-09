/-!
# `func (z *Int) Mod(x, y *Int) *Int`

`z.Mod(x, y)` sets `z = x mod y` (the remainder of unsigned integer division) and returns `z`.
A zero modulus is NOT an error and does not panic: the result is `0`.
-/

namespace Fv256.Spec

/-- Value of `z.Mod(x, y)`: the remainder `x % y`, and `0` when `y = 0`. -/
def mod (x y : Nat) : Nat := if y = 0 then 0 else x % y

/-- The remainder of `7 / 3`. -/
example : mod 7 3 = 1 := by decide

/-- A zero modulus yields zero (no panic). -/
example : mod 7 0 = 0 := by decide

end Fv256.Spec
