/-!
# `func (z *Int) And(x, y *Int) *Int`

`z.And(x, y)` sets `z` to the bitwise AND of `x` and `y` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.And(x, y)`: bit `i` of the result is set exactly when bit `i` is set in both `x` and `y`. -/
def and (x y : Nat) : Nat := x &&& y

/-- 12 AND 10 = 8. -/
example : and 12 10 = 8 := by decide

/-- AND with zero is zero. -/
example : and 12 0 = 0 := by decide

end Fv256.Spec
