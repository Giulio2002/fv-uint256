/-!
# `func (z *Int) Gt(x *Int) bool`

`z.Gt(x)` reports whether `z > x`, comparing both as unsigned integers. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Gt(x)`: `true` exactly when `x > y` as natural numbers (unsigned order). -/
def gt (x y : Nat) : Bool := decide (y < x)

example : gt 5 3 = true := by decide
example : gt 5 5 = false := by decide

end Fv256.Spec
