/-!
# `func (z *Int) AddUint64(x *Int, y uint64) *Int`

`z.AddUint64(x, n)` sets `z = x + n` with wrap-around (modulo `2^256`) and returns `z`; `n` is a 64-bit unsigned number. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.AddUint64(x, n)`: the sum of the 256-bit number `x` and the 64-bit number `n`, wrapped modulo `2^256`. -/
def addU (x n : Nat) : Nat := (x + n) % 2 ^ 256

/-- Wrap-around. -/
example : addU (2 ^ 256 - 1) 2 = 1 := by decide

/-- Small numbers add as usual. -/
example : addU 40 2 = 42 := by decide

end Fv256.Spec
