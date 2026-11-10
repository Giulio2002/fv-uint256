import Fv256.Spec.Rsh

/-!
# `func (z *Int) IRsh(n uint) *Int`

`z.IRsh(n)` is the in-place logical right shift: `z = z >> n`, the same as `z.Rsh(z, n)`. Its value is `Fv256.Spec.rsh` of the old `z`
(see `Fv256/Spec/Rsh.lean`). There is no error or panic case.
-/

namespace Fv256.Spec

/-- The in-place form uses the same specification: `z.IRsh(n)` leaves `rsh z n` in `z` (checked on a small case). -/
example : rsh 12 2 = 3 := by decide

end Fv256.Spec
