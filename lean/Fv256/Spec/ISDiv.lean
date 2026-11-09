import Fv256.Spec.SDiv

/-!
# `func (z *Int) ISDiv(d *Int) *Int`

`z.ISDiv(d)` is `z.SDiv(z, d)`: signed (two's complement) division of `z` by `d`, truncating toward zero, stored back in `z`.
Division by zero is NOT an error and does not panic: `z` becomes `0`; `-2^255 / -1` wraps to `-2^255`.
-/

namespace Fv256.Spec

/-- Value of `z.ISDiv(d)` given the old value `z` of the receiver: `Spec.sdiv z d`. -/
def isdiv (z d : Nat) : Nat := sdiv z d

/-- `-7 / 2 = -3` (truncation toward zero). -/
example : isdiv (2 ^ 256 - 7) 2 = 2 ^ 256 - 3 := by decide

end Fv256.Spec
