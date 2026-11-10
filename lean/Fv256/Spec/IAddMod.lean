import Fv256.Spec.AddMod

/-!
# `func (z *Int) IAddMod(x, m *Int) *Int`

`z.IAddMod(x, m)` is the in-place form of `AddMod`: it sets `z = (z + x) mod m` and returns `z`. The sum is exact (no wrap-around
before the reduction), and a zero modulus is not an error: the result is `0`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.IAddMod(x, m)`, where `z` is the receiver's value BEFORE the call: `AddMod` with the receiver as the first summand. -/
def iAddMod (z x m : Nat) : Nat := addMod z x m

/-- The receiver is the first summand: `(5 + 4) mod 7 = 2`. -/
example : iAddMod 5 4 7 = 2 := by decide

/-- A zero modulus gives zero. -/
example : iAddMod 5 4 0 = 0 := by decide

end Fv256.Spec
