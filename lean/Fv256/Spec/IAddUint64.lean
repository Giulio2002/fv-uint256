/-!
# `func (z *Int) IAddUint64(n uint64) *Int`

`z.IAddUint64(n)` adds the 64-bit number `n` to `z` in place: `z = z + n` with wrap-around (modulo `2^256`), and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- New value of `z` after `z.IAddUint64(n)`, where `z` is its value before the call: the sum wrapped modulo `2^256`. -/
def iAddU (z n : Nat) : Nat := (z + n) % 2 ^ 256

/-- Wrap-around. -/
example : iAddU (2 ^ 256 - 1) 2 = 1 := by decide

/-- Small numbers add as usual. -/
example : iAddU 40 2 = 42 := by decide

end Fv256.Spec
