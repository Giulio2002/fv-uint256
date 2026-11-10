import Fv256.Spec.Div

/-!
# `func (z *Int) IDiv(x *Int) *Int`

`z.IDiv(x)` divides `z` by `x` in place: it is `z.Div(z, x)` (unsigned, rounded down) and returns `z`.
Division by zero is NOT an error and does not panic: `z` becomes `0`.
-/

namespace Fv256.Spec

/-- Value of `z.IDiv(x)` given the old value `z` of the receiver: `Spec.div z x`. -/
def idiv (z x : Nat) : Nat := div z x

/-- Rounds down. -/
example : idiv 7 2 = 3 := by decide

/-- Dividing by zero yields zero (no panic). -/
example : idiv 7 0 = 0 := by decide

end Fv256.Spec
