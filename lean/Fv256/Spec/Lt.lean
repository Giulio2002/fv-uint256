/-!
# `func (z *Int) Lt(x *Int) bool`

`z.Lt(x)` reports whether `z < x`, comparing both as unsigned integers. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Lt(x)`: `true` exactly when `x < y` as natural numbers (unsigned order). -/
def lt (x y : Nat) : Bool := decide (x < y)

example : lt 3 5 = true := by decide
example : lt 5 5 = false := by decide

/-- Unsigned order: a number with the top bit set is LARGER than one without it. -/
example : lt 1 (2 ^ 255) = true := by decide

end Fv256.Spec
