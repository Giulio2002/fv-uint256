import Fv256.Spec.SMod

/-!
# `func (z *Int) ISMod(x *Int) *Int`

`z.ISMod(x)` is `z.SMod(z, x)`: `z` becomes `sign(z) * (|z| mod |x|)` with both operands read as two's complement integers.
A zero `x` is NOT an error and does not panic: `z` becomes `0`.
-/

namespace Fv256.Spec

/-- Value of `z.ISMod(x)` given the old value `z` of the receiver: `Spec.smod z x`. -/
def ismod (z x : Nat) : Nat := smod z x

/-- `-7 mod 3 = -1` (the sign follows the dividend). -/
example : ismod (2 ^ 256 - 7) 3 = 2 ^ 256 - 1 := by decide

end Fv256.Spec
