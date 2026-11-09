/-!
# `func (z *Int) Or(x, y *Int) *Int`

`z.Or(x, y)` sets `z` to the bitwise OR of `x` and `y` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Or(x, y)`: bit `i` of the result is set exactly when bit `i` is set in `x` or in `y` (or both). -/
def or (x y : Nat) : Nat := x ||| y

/-- 12 OR 10 = 14. -/
example : or 12 10 = 14 := by decide

/-- OR with zero is the identity. -/
example : or 12 0 = 12 := by decide

end Fv256.Spec
