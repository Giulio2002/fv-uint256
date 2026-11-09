/-!
# `func (z *Int) Add(x, y *Int) *Int`

`z.Add(x, y)` sets `z = x + y` with wrap-around (arithmetic modulo `2^256`) and returns `z`.
It has no error or panic case: every pair of inputs is valid.
-/

namespace Fv256.Spec

/-- Value of `z.Add(x, y)`: the sum, wrapped modulo `2^256` (so `2^256 - 1 + 1 = 0`). -/
def add (x y : Nat) : Nat := (x + y) % 2 ^ 256

/-- Wrap-around: the largest word plus one is zero. -/
example : add (2 ^ 256 - 1) 1 = 0 := by decide

/-- Small numbers add as usual. -/
example : add 2 3 = 5 := by decide

end Fv256.Spec
