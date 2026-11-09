/-!
# `func (z *Int) SubUint64(x *Int, y uint64) *Int`

`z.SubUint64(x, n)` sets `z = x - n` with wrap-around (modulo `2^256`) and returns `z`; `n` is a 64-bit unsigned number. It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.SubUint64(x, n)`: the difference of the 256-bit number `x` and the 64-bit number `n`, wrapped modulo `2^256`. -/
def subU (x n : Nat) : Nat := (x + 2 ^ 256 - n) % 2 ^ 256

/-- Wrap-around. -/
example : subU 0 1 = 2 ^ 256 - 1 := by decide

/-- Small numbers subtract as usual. -/
example : subU 44 2 = 42 := by decide

end Fv256.Spec
