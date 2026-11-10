import Fv256.Spec.MulModWithReciprocal

/-!
# `func (z *Int) IMulModWithReciprocal(x, m *Int, mu *[5]uint64) *Int`

`z.IMulModWithReciprocal(x, m, mu)` is the in-place form of `MulModWithReciprocal`: it sets `z = (z * x) mod m` (exact product, `0`
for `m = 0`), using the caller-supplied reciprocal `mu` of `m` (the promise is `Spec.muOk m mu`). No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.IMulModWithReciprocal(x, m, mu)` (when `muOk m mu`), where `z` is the receiver's value BEFORE the call. -/
def iMulModWithReciprocal (z x m : Nat) : Nat := mulModWithReciprocal z x m

/-- The receiver is the first factor: `(5 * 4) mod 7 = 6`. -/
example : iMulModWithReciprocal 5 4 7 = 6 := by decide

end Fv256.Spec
