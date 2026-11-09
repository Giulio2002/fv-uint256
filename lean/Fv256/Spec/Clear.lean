/-!
# `func (z *Int) Clear() *Int`

`z.Clear()` sets `z = 0` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Clear()`: zero. -/
def clear : Nat := 0

/-- Clear yields zero. -/
example : clear = 0 := by decide

end Fv256.Spec
