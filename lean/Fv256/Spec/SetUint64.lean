/-!
# `func (z *Int) SetUint64(x uint64) *Int`

`z.SetUint64(n)` sets `z` to the 64-bit unsigned number `n` (the upper 192 bits are zero) and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.SetUint64(n)`: the number `n` (a 64-bit value, so it always fits in 256 bits). -/
def setU (n : Nat) : Nat := n

/-- SetUint64 stores the number as is. -/
example : setU 42 = 42 := by decide

end Fv256.Spec
