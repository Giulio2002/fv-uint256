/-!
# `func (z *Int) Sub(x, y *Int) *Int`

`z.Sub(x, y)` sets `z = x - y` with wrap-around (arithmetic modulo `2^256`) and returns `z`; so `0 - 1 = 2^256 - 1`. It has no error or panic case: every pair of inputs is valid.
-/

namespace Fv256.Spec

/-- Value of `z.Sub(x, y)` for 256-bit `x`, `y`: the difference wrapped modulo `2^256` (adding `2^256` first keeps the natural-number subtraction from truncating at zero). -/
def sub (x y : Nat) : Nat := (x + 2 ^ 256 - y) % 2 ^ 256

/-- Wrap-around: zero minus one is the largest word. -/
example : sub 0 1 = 2 ^ 256 - 1 := by decide

/-- Small numbers subtract as usual. -/
example : sub 5 3 = 2 := by decide

end Fv256.Spec
