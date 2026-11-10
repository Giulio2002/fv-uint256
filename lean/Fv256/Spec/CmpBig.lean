/-!
# `func (z *Int) CmpBig(x *big.Int) (r int)`

`z.CmpBig(x)` compares the unsigned number `z` with the integer `x` (of either sign, any size) and returns `-1` if `z < x`,
`0` if `z = x`, `+1` if `z > x`. It never panics (for non-nil `x`) and does not modify `z` or `x`.
-/

namespace Fv256.Spec

/-- The result of `z.CmpBig(x)` for the number `z` held in the receiver and the integer value `x` of the `big.Int`. -/
def cmpBig (z : Nat) (x : Int) : Int := if (z : Int) < x then -1 else if (z : Int) = x then 0 else 1

/-- A negative `x` is always smaller than any `z`. -/
example : cmpBig 0 (-1) = 1 := by decide

/-- Equal values compare equal. -/
example : cmpBig 7 7 = 0 := by decide

/-- A `x` above `2^256` is larger than every `z`. -/
example : cmpBig (2 ^ 256 - 1) (2 ^ 256) = -1 := by decide

end Fv256.Spec
