/-!
# `func (z *Int) AddMod(x, y, m *Int) *Int`

`z.AddMod(x, y, m)` sets `z = (x + y) mod m` and returns `z`. The sum is computed WITHOUT wrap-around (a 257-bit sum is fine),
so the result is the true remainder. A zero modulus is not an error: the result is `0`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.AddMod(x, y, m)`: `0` when `m = 0`, otherwise the remainder of the exact sum `x + y` modulo `m`. -/
def addMod (x y m : Nat) : Nat := if m = 0 then 0 else (x + y) % m

/-- The sum is not truncated to 256 bits first: `(2^256 - 1) + (2^256 - 1) = 2^257 - 2`, so a small case is checked here. -/
example : addMod 5 4 7 = 2 := by decide

/-- A zero modulus gives zero. -/
example : addMod 5 4 0 = 0 := by decide

/-- No truncation of the intermediate sum: `x + y` may exceed `2^256`. -/
example : addMod (2 ^ 256 - 1) (2 ^ 256 - 1) (2 ^ 256) = 2 ^ 256 - 2 := by decide

end Fv256.Spec
