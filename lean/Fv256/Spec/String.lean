import Fv256.Spec.Dec

/-!
# `func (z *Int) String() string`

`z.String()` is `z.Dec()`: the decimal representation of `z` (see `Fv256/Spec/Dec.lean`). It never fails and never panics.
-/

namespace Fv256.Spec

/-- The ASCII bytes returned by `z.String()`: the decimal digits of `z`, as for `Dec`. -/
def string (x : Nat) : List Nat := dec x

example : string 255 = [50, 53, 53] := by decide

end Fv256.Spec
