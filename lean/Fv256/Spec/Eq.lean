/-!
# `func (z *Int) Eq(x *Int) bool`

`z.Eq(x)` reports whether the two numbers are equal. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Eq(x)`: `true` exactly when the two numbers are equal. -/
def eq (x y : Nat) : Bool := x == y

example : eq 4 4 = true := by decide
example : eq 4 5 = false := by decide

end Fv256.Spec
