import Fv256.Spec.Signed

/-!
# `func (z *Int) Sgt(x *Int) bool`

`z.Sgt(x)` reports whether `z > x` when both are read as signed two's-complement numbers. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Sgt(x)`: `true` exactly when the signed reading of `x` is above the signed reading of `y`. -/
def sgt (x y : Nat) : Bool := decide (signed y < signed x)

/-- `1 > -1`, although `1` is the numerically smaller bit pattern. -/
example : sgt 1 (2 ^ 256 - 1) = true := by decide

example : sgt (2 ^ 256 - 1) 1 = false := by decide
example : sgt 3 3 = false := by decide

end Fv256.Spec
