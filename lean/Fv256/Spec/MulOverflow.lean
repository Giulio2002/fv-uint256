import Fv256.Spec.Mul

/-!
# `func (z *Int) MulOverflow(x, y *Int) (*Int, bool)`

`z.MulOverflow(x, y)` sets `z` to the product `x * y` wrapped modulo `2^256` (exactly the value of `Mul`) and returns `z`
together with a flag that is `true` if and only if the exact product does not fit in 256 bits.
It has no error or panic case.
-/

namespace Fv256.Spec

/-- The overflow flag returned by `z.MulOverflow(x, y)`: the exact (unwrapped) product `x * y` is at least `2^256`.
The value left in `z` is `Fv256.Spec.mul x y`. -/
abbrev mulOverflows (x y : Nat) : Prop := 2 ^ 256 ≤ x * y

/-- `2^128 * 2^128 = 2^256` is the smallest square that overflows. -/
example : mulOverflows (2 ^ 128) (2 ^ 128) := by decide

/-- `(2^128 - 1)^2 < 2^256`: no overflow. -/
example : ¬ mulOverflows (2 ^ 128 - 1) (2 ^ 128 - 1) := by decide

/-- On overflow the stored value is the wrapped product. -/
example : mul (2 ^ 128) (2 ^ 128 + 1) = 2 ^ 128 := by decide

end Fv256.Spec
