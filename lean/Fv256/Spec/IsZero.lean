/-!
# `func (z *Int) IsZero() bool`

`z.IsZero()` reports whether `z` is zero. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.IsZero()`: `true` exactly when the number is `0`. -/
def isZero (x : Nat) : Bool := x == 0

example : isZero 0 = true := by decide
example : isZero (2 ^ 255) = false := by decide

end Fv256.Spec
