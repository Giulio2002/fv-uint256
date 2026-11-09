import Fv256.Spec.MulMod

/-!
# `func (z *Int) IMulMod(x, m *Int) *Int`

`z.IMulMod(x, m)` is the in-place form of `MulMod`: it sets `z = (z * x) mod m` and returns `z`. The product is exact (no wrap-around
before the reduction), and a zero modulus is not an error: the result is `0`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.IMulMod(x, m)`, where `z` is the receiver's value BEFORE the call: `MulMod` with the receiver as the first factor. -/
def iMulMod (z x m : Nat) : Nat := mulMod z x m

/-- The receiver is the first factor: `(5 * 4) mod 7 = 6`. -/
example : iMulMod 5 4 7 = 6 := by decide

/-- A zero modulus gives zero. -/
example : iMulMod 5 4 0 = 0 := by decide

end Fv256.Spec
