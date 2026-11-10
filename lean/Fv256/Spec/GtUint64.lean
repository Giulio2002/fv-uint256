import Fv256.Spec.Gt

/-!
# `func (z *Int) GtUint64(n uint64) bool`

`z.GtUint64(n)` reports whether `z > n`, comparing as unsigned integers (`Fv256.Spec.gt z n`; `n` is a small natural number).
It has no error or panic case. This function adds no definition of its own: its specification IS `Fv256.Spec.gt`.
-/

namespace Fv256.Spec

/-- A number needing more than 64 bits is above every 64-bit `n`. -/
example : gt (2 ^ 64) (2 ^ 64 - 1) = true := by decide

example : gt 4 4 = false := by decide

end Fv256.Spec
