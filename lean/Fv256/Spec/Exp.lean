/-!
# `func (z *Int) Exp(base, exponent *Int) *Int`

`z.Exp(base, exponent)` sets `z = base ^ exponent` with wrap-around (arithmetic modulo `2^256`) and returns `z`.
`Exp(x, 0)` is `1` for every `x`, including `0`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.Exp(base, exponent)`: the exact power, reduced modulo `2^256`. -/
def exp (base exponent : Nat) : Nat := base ^ exponent % 2 ^ 256

/-- `2^10 = 1024`. -/
example : exp 2 10 = 1024 := by decide

/-- Wrap-around: `2^256 = 0` (modulo `2^256`). -/
example : exp 2 256 = 0 := by decide

/-- Anything to the power zero is one, also zero. -/
example : exp 0 0 = 1 := by decide

end Fv256.Spec
