import Fv256.Spec.BigEndian

/-!
# `func (z *Int) MarshalSSZ() ([]byte, error)`

`z.MarshalSSZ()` returns a freshly allocated 32-byte slice holding the SSZ encoding of `z` (the value as 32 bytes,
LITTLE-endian), and a nil error. It cannot fail.
-/

namespace Fv256.Spec

/-- The contents of the slice `z.MarshalSSZ()` returns for the number `x` held in `z`: `x` in 32 little-endian bytes. -/
def marshalSSZ (x : Nat) : List Nat := leBytes 32 x

/-- One is `01 00 … 00`: the least significant byte first. -/
example : marshalSSZ 1 = 1 :: List.replicate 31 0 := by decide

/-- A 256-bit value always encodes to 32 bytes. -/
example : (marshalSSZ (2 ^ 256 - 1)).length = 32 := by decide

end Fv256.Spec
