import Fv256.Spec.SRsh

/-!
# `func (z *Int) ISRsh(n uint) *Int`

`z.ISRsh(n)` is the in-place arithmetic right shift: `z = z >>s n`, the same as `z.SRsh(z, n)`. Its value is `Fv256.Spec.srsh` of the
old `z` (see `Fv256/Spec/SRsh.lean`). There is no error or panic case.
-/

namespace Fv256.Spec

/-- The in-place form uses the same specification: `z.ISRsh(n)` leaves `srsh z n` in `z` (checked on a small case). -/
example : srsh (2 ^ 256 - 4) 1 = 2 ^ 256 - 2 := by decide

end Fv256.Spec
