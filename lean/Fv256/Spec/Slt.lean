import Fv256.Spec.Signed

/-!
# `func (z *Int) Slt(x *Int) bool`

`z.Slt(x)` reports whether `z < x` when both are read as signed two's-complement numbers. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Slt(x)`: `true` exactly when the signed reading of `x` is below the signed reading of `y`. -/
def slt (x y : Nat) : Bool := decide (signed x < signed y)

/-- `-1 < 1`, although `-1` is the numerically larger bit pattern. -/
example : slt (2 ^ 256 - 1) 1 = true := by decide

example : slt 1 (2 ^ 256 - 1) = false := by decide
example : slt 3 3 = false := by decide

end Fv256.Spec
