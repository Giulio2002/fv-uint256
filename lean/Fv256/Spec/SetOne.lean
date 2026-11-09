/-!
# `func (z *Int) SetOne() *Int`

`z.SetOne()` sets `z = 1` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.SetOne()`: one. -/
def one : Nat := 1

/-- SetOne yields one. -/
example : one = 1 := by decide

end Fv256.Spec
