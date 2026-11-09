/-!
# `func (z *Int) Set(x *Int) *Int`

`z.Set(x)` copies `x` into `z` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Set(x)`: the number `x`, unchanged. -/
def set (x : Nat) : Nat := x

/-- Set copies the number. -/
example : set 42 = 42 := by decide

end Fv256.Spec
