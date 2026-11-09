/-!
# `func (z *Int) Mul(x, y *Int) *Int`

`z.Mul(x, y)` sets `z = x * y` with wrap-around (arithmetic modulo `2^256`, i.e. the low 256 bits of the product) and returns `z`.
It has no error or panic case: every pair of inputs is valid.
-/

namespace Fv256.Spec

/-- Value of `z.Mul(x, y)`: the product, wrapped modulo `2^256`. -/
def mul (x y : Nat) : Nat := (x * y) % 2 ^ 256

/-- Small numbers multiply as usual. -/
example : mul 6 7 = 42 := by decide

/-- Wrap-around: `2^255 * 2 = 2^256`, which is `0` modulo `2^256`. -/
example : mul (2 ^ 255) 2 = 0 := by decide

/-- The largest word times itself is `1` (since `(-1) * (-1) = 1` modulo `2^256`). -/
example : mul (2 ^ 256 - 1) (2 ^ 256 - 1) = 1 := by decide

end Fv256.Spec
