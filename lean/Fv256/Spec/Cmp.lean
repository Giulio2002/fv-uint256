/-!
# `func (z *Int) Cmp(x *Int) (r int)`

`z.Cmp(x)` compares the two numbers as unsigned integers and returns `-1` if `z < x`, `0` if `z = x` and `+1` if `z > x`.
It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Cmp(x)` (also of `z.CmpUint64(n)`): the three-way unsigned comparison of `x` against `y`, as `-1`, `0` or `1`. -/
def cmp (x y : Nat) : Int := if x < y then -1 else if x = y then 0 else 1

/-- Smaller gives `-1`. -/
example : cmp 3 5 = -1 := by decide

/-- Equal gives `0`. -/
example : cmp 5 5 = 0 := by decide

/-- Larger gives `+1`. -/
example : cmp 7 5 = 1 := by decide

end Fv256.Spec
