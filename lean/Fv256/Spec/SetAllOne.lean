/-!
# `func (z *Int) SetAllOne() *Int`

`z.SetAllOne()` sets all 256 bits of `z` to one, i.e. `z = 2^256 - 1`, and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.SetAllOne()`: the largest 256-bit number, `2^256 - 1` (all bits set). -/
def allOne : Nat := 2 ^ 256 - 1

/-- One more than all ones is `2^256`. -/
example : allOne + 1 = 2 ^ 256 := by decide

end Fv256.Spec
