import Fv256.Spec.MulDivOverflow

/-!
# `func (z *Int) MulDivOverflowRem(x, y, d, m *Int) (*Int, *Int, bool)`

`z.MulDivOverflowRem(x, y, d, m)` is `MulDivOverflow` that also reports the remainder: `z` receives the low 256 bits of
`x * y / d` (full 512-bit product), the number at `m` is overwritten with the remainder `x * y mod d`, and the call returns
`z`, `m` and the overflow flag (the quotient does not fit in 256 bits). For `d = 0`: `z` is `0`, the remainder is `0` and the
flag is `false`. No call panics. The output `m` must be a non-nil object that does not overlap `z`, `x`, `y` or `d`.
-/

namespace Fv256.Spec

/-- Value left in `z`: exactly as for `MulDivOverflow`. -/
def mulDivOverflowRemQuot (x y d : Nat) : Nat := mulDivOverflow x y d

/-- Value left in `*m`: the remainder of the exact product, `x * y mod d` (`0` when `d = 0`). -/
def mulDivOverflowRem (x y d : Nat) : Nat := mulMod x y d

/-- `7 * 5 = 35 = 4 * 8 + 3`: quotient 4, remainder 3. -/
example : mulDivOverflowRemQuot 7 5 8 = 4 ∧ mulDivOverflowRem 7 5 8 = 3 := by decide

/-- Division by zero: quotient `0`, remainder `0`. -/
example : mulDivOverflowRemQuot 7 5 0 = 0 ∧ mulDivOverflowRem 7 5 0 = 0 := by decide

end Fv256.Spec
