import Fv256.Spec.Cmp

/-!
# `func (z *Int) CmpUint64(n uint64) int`

`z.CmpUint64(n)` compares `z` with the 64-bit number `n` as unsigned integers and returns `-1`, `0` or `+1` exactly as
`z.Cmp` does (`Fv256.Spec.cmp z n`; the number `n` is just a small natural number). It has no error or panic case.
This function adds no definition of its own: its specification IS `Fv256.Spec.cmp`.
-/

namespace Fv256.Spec

/-- A 256-bit value above every 64-bit `n` compares as `+1`. -/
example : cmp (2 ^ 64) (2 ^ 64 - 1) = 1 := by decide

/-- Equal values compare as `0`. -/
example : cmp 9 9 = 0 := by decide

end Fv256.Spec
