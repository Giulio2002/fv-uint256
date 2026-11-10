import Fv256.Spec.Lsh

/-!
# `func (z *Int) ILsh(n uint) *Int`

`z.ILsh(n)` is the in-place left shift: `z = z << n`, the same as `z.Lsh(z, n)`. Its value is `Fv256.Spec.lsh` of the old `z`
(see `Fv256/Spec/Lsh.lean`). There is no error or panic case.
-/

namespace Fv256.Spec

/-- The in-place form uses the same specification: `z.ILsh(n)` leaves `lsh z n` in `z` (checked on a small case). -/
example : lsh 3 2 = 12 := by decide

end Fv256.Spec
