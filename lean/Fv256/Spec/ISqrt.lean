import Fv256.Spec.Sqrt

/-!
# `func (z *Int) ISqrt() *Int`

`z.ISqrt()` is the in-place integer square root: `z = ⌊√z⌋`, the same as `z.Sqrt(z)`. The new value of `z` is a number `r` with
`Fv256.Spec.IsSqrt (old z) r` (see `Fv256/Spec/Sqrt.lean`). There is no error or panic case.
-/

namespace Fv256.Spec

/-- The in-place form uses the same specification (checked on a small case: `⌊√10⌋ = 3`). -/
example : IsSqrt 10 3 := by decide

end Fv256.Spec
