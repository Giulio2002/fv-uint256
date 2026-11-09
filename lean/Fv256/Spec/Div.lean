/-!
# `func (z *Int) Div(x, y *Int) *Int`

`z.Div(x, y)` sets `z = x / y` (unsigned integer division, rounded down) and returns `z`.
Division by zero is NOT an error and does not panic: the result is `0`.
-/

namespace Fv256.Spec

/-- Value of `z.Div(x, y)`: the quotient `x / y` rounded down, and `0` when `y = 0`. -/
def div (x y : Nat) : Nat := if y = 0 then 0 else x / y

/-- Rounds down. -/
example : div 7 2 = 3 := by decide

/-- Dividing by zero yields zero (no panic). -/
example : div 7 0 = 0 := by decide

end Fv256.Spec
