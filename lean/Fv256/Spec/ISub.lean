/-!
# `func (z *Int) ISub(x *Int) *Int`

`z.ISub(x)` subtracts `x` from `z` in place: `z = z - x` with wrap-around (modulo `2^256`), and returns `z`. It is `z.Sub(z, x)`. No error or panic case.
-/

namespace Fv256.Spec

/-- New value of `z` after `z.ISub(x)`, where `z` is its value before the call: the difference wrapped modulo `2^256`. -/
def iSub (z x : Nat) : Nat := (z + 2 ^ 256 - x) % 2 ^ 256

/-- Wrap-around. -/
example : iSub 0 1 = 2 ^ 256 - 1 := by decide

/-- Small numbers subtract as usual. -/
example : iSub 5 3 = 2 := by decide

end Fv256.Spec
