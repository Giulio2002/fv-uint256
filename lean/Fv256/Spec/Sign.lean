/-!
# `func (z *Int) Sign() int`

`z.Sign()` reads `z` as a signed two's-complement number and returns `0` if it is zero, `+1` if it is positive and `-1` if it is
negative (top bit, bit 255, set). It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Sign()`: `0` for zero, `1` for a number below `2^255`, `-1` for a number of `2^255` or more. -/
def sign (x : Nat) : Int := if x = 0 then 0 else if x < 2 ^ 255 then 1 else -1

example : sign 0 = 0 := by decide
example : sign 7 = 1 := by decide
example : sign (2 ^ 255 - 1) = 1 := by decide
example : sign (2 ^ 255) = -1 := by decide

end Fv256.Spec
