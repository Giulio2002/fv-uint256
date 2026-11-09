/-!
# `func (z *Int) ISubUint64(n uint64) *Int`

`z.ISubUint64(n)` subtracts the 64-bit number `n` from `z` in place: `z = z - n` with wrap-around (modulo `2^256`), and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- New value of `z` after `z.ISubUint64(n)`, where `z` is its value before the call: the difference wrapped modulo `2^256`. -/
def iSubU (z n : Nat) : Nat := (z + 2 ^ 256 - n) % 2 ^ 256

/-- Wrap-around. -/
example : iSubU 0 1 = 2 ^ 256 - 1 := by decide

/-- Small numbers subtract as usual. -/
example : iSubU 44 2 = 42 := by decide

end Fv256.Spec
