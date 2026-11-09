import Fv256.Spec.Lt

/-!
# `func (z *Int) LtUint64(n uint64) bool`

`z.LtUint64(n)` reports whether `z < n`, comparing as unsigned integers (`Fv256.Spec.lt z n`; `n` is a small natural number).
It has no error or panic case. This function adds no definition of its own: its specification IS `Fv256.Spec.lt`.
-/

namespace Fv256.Spec

/-- A number needing more than 64 bits is never below a 64-bit `n`. -/
example : lt (2 ^ 64) (2 ^ 64 - 1) = false := by decide

example : lt 3 4 = true := by decide

end Fv256.Spec
