import Fv256.Spec.Mul

/-!
# `func (z *Int) IMul(x *Int) *Int`

`z.IMul(x)` multiplies `z` by `x` in place: it is `z.Mul(z, x)` (wrap-around modulo `2^256`) and returns `z`.
It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.IMul(x)` given the old value `z` of the receiver: `Spec.mul z x`. -/
def imul (z x : Nat) : Nat := mul z x

/-- Small numbers multiply as usual. -/
example : imul 6 7 = 42 := by decide

end Fv256.Spec
