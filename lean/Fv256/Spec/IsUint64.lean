/-!
# `func (z *Int) IsUint64() bool`

`z.IsUint64()` reports whether `z` fits in 64 bits, i.e. `z < 2^64`. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.IsUint64()`: `true` exactly when the number is below `2^64`. -/
def isUint64 (x : Nat) : Bool := decide (x < 2 ^ 64)

example : isUint64 (2 ^ 64 - 1) = true := by decide
example : isUint64 (2 ^ 64) = false := by decide

end Fv256.Spec
