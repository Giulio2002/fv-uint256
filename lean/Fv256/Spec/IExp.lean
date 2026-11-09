import Fv256.Spec.Exp

/-!
# `func (z *Int) IExp(exponent *Int) *Int`

`z.IExp(x)` is the in-place form of `Exp`: it sets `z = z ^ x` modulo `2^256` (the receiver is the base, the argument the exponent) and
returns `z`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.IExp(x)`, where `z` is the receiver's value BEFORE the call (the base): `Exp` with the receiver as the base. -/
def iExp (z x : Nat) : Nat := exp z x

/-- `3^4 = 81`. -/
example : iExp 3 4 = 81 := by decide

end Fv256.Spec
