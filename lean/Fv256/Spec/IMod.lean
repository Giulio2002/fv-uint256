import Fv256.Spec.Mod

/-!
# `func (z *Int) IMod(x *Int) *Int`

`z.IMod(x)` reduces `z` modulo `x` in place: it is `z.Mod(z, x)` (unsigned remainder) and returns `z`.
A zero modulus is NOT an error and does not panic: `z` becomes `0`.
-/

namespace Fv256.Spec

/-- Value of `z.IMod(x)` given the old value `z` of the receiver: `Spec.mod z x`. -/
def imod (z x : Nat) : Nat := mod z x

/-- The remainder of `7 / 3`. -/
example : imod 7 3 = 1 := by decide

/-- A zero modulus yields zero (no panic). -/
example : imod 7 0 = 0 := by decide

end Fv256.Spec
