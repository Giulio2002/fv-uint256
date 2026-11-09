/-!
# `func (*Int) SizeSSZ() int`

`z.SizeSSZ()` returns the size in bytes of the SSZ encoding of a `uint256`: always 32, whatever `z` holds (the receiver is not
even read). No error or panic case.
-/

namespace Fv256.Spec

/-- The value of `z.SizeSSZ()`: the SSZ encoding of a `uint256` is 32 bytes. -/
def sizeSSZ : Nat := 32

/-- A 256-bit integer is 32 bytes. -/
example : sizeSSZ = 256 / 8 := by decide

end Fv256.Spec
