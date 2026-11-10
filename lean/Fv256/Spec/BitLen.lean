/-!
# `func (z *Int) BitLen() int`

`z.BitLen()` returns the number of bits needed to write `z` in binary without leading zeros: `0` for zero, otherwise the position
of the highest set bit plus one (`1..256`). It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.BitLen()`: `0` for zero, otherwise `⌊log₂ x⌋ + 1`. -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

example : bitLen 0 = 0 := by decide
example : bitLen 1 = 1 := by decide
example : bitLen 255 = 8 := by decide
example : bitLen 256 = 9 := by decide
example : bitLen (2 ^ 256 - 1) = 256 := by decide

end Fv256.Spec
