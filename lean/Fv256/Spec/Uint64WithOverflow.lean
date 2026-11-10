import Fv256.Spec.Uint64

/-!
# `func (z *Int) Uint64WithOverflow() (uint64, bool)`

`z.Uint64WithOverflow()` returns the low 64 bits of `z` (`Fv256.Spec.uint64`, the value modulo `2^64`) and a flag that is `true`
exactly when `z` does not fit in 64 bits (so bits were dropped). It has no error or panic case.
-/

namespace Fv256.Spec

/-- The overflow flag of `z.Uint64WithOverflow()`: `true` exactly when the number is `2^64` or more. -/
def uint64Ov (x : Nat) : Bool := decide (2 ^ 64 ≤ x)

example : uint64Ov (2 ^ 64 - 1) = false := by decide
example : uint64Ov (2 ^ 64) = true := by decide

/-- The pair for an overflowing number: truncated value and `true`. -/
example : (uint64 (2 ^ 64 + 5), uint64Ov (2 ^ 64 + 5)) = (5, true) := by decide

end Fv256.Spec
