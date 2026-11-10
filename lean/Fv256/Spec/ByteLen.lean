import Fv256.Spec.BitLen

/-!
# `func (z *Int) ByteLen() int`

`z.ByteLen()` returns the number of bytes needed to write `z` without leading zero bytes: `0` for zero, otherwise the bit length
rounded up to whole bytes (`1..32`). It has no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.ByteLen()`: the bit length (`Fv256.Spec.bitLen`) rounded up to a multiple of 8, divided by 8. -/
def byteLen (x : Nat) : Nat := (bitLen x + 7) / 8

example : byteLen 0 = 0 := by decide
example : byteLen 255 = 1 := by decide
example : byteLen 256 = 2 := by decide
example : byteLen (2 ^ 256 - 1) = 32 := by decide

end Fv256.Spec
