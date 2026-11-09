/-!
# `func (z *Int) AddOverflow(x, y *Int) (*Int, bool)`

`z.AddOverflow(x, y)` sets `z = x + y` wrapped modulo `2^256` (exactly the value of `Add`) and returns `z` together with an overflow flag. The flag is true exactly when the true sum does not fit in 256 bits (`x + y >= 2^256`). It has no error or panic case.
-/

namespace Fv256.Spec

/-- Overflow flag of `z.AddOverflow(x, y)`: true exactly when the exact sum `x + y` needs more than 256 bits. (The stored value is `Fv256.Spec.add x y`.) -/
def addOv (x y : Nat) : Bool := decide (2 ^ 256 ≤ x + y)

/-- The largest word plus one overflows. -/
example : addOv (2 ^ 256 - 1) 1 = true := by decide

/-- Small sums do not overflow. -/
example : addOv 2 3 = false := by decide

/-- The largest word plus zero does not overflow. -/
example : addOv (2 ^ 256 - 1) 0 = false := by decide

end Fv256.Spec
