import Fv256.Spec.MulMod

/-!
# `func (z *Int) MulDivOverflow(x, y, d *Int) (*Int, bool)`

`z.MulDivOverflow(x, y, d)` computes `x * y / d` from the FULL 512-bit product (no wrap-around in the multiplication), stores the low
256 bits of the quotient in `z`, and returns `z` and an overflow flag that is `true` exactly when the quotient does not fit in
256 bits. Division by zero is not an error and does not panic: `z` is `0` and the flag is `false`.
-/

namespace Fv256.Spec

/-- Value left in `z` by `z.MulDivOverflow(x, y, d)`: the quotient `x * y / d` of the exact product, truncated to 256 bits; `0` when `d = 0`. -/
def mulDivOverflow (x y d : Nat) : Nat := if d = 0 then 0 else (x * y / d) % 2 ^ 256

/-- The overflow flag returned by `MulDivOverflow`: the exact quotient `x * y / d` is `2^256` or more; `false` when `d = 0`. -/
def mulDivOverflowFlag (x y d : Nat) : Bool := if d = 0 then false else decide (2 ^ 256 ≤ x * y / d)

/-- `(2^256 - 1) * 4 / 2 = 2^257 - 2`: the low 256 bits are `2^256 - 2` and the quotient overflowed. -/
example : mulDivOverflow (2 ^ 256 - 1) 4 2 = 2 ^ 256 - 2 := by decide

example : mulDivOverflowFlag (2 ^ 256 - 1) 4 2 = true := by decide

/-- A small quotient does not overflow: `6 * 7 / 3 = 14`. -/
example : mulDivOverflow 6 7 3 = 14 ∧ mulDivOverflowFlag 6 7 3 = false := by decide

/-- Division by zero: value `0`, no overflow. -/
example : mulDivOverflow 6 7 0 = 0 ∧ mulDivOverflowFlag 6 7 0 = false := by decide

end Fv256.Spec
