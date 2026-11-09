import Fv256.Spec.BigEndian

/-!
# `func (z *Int) WriteToArray32(dest *[32]byte)`

`z.WriteToArray32(dest)` overwrites the 32 bytes of `*dest` with `z` in BIG-endian order (leading zero bytes included).
Nothing else is written. No error or panic case.
-/

namespace Fv256.Spec

/-- The 32 bytes `*dest` holds after `z.WriteToArray32(dest)`, for the number `x` held in `z`: `x` in 32 big-endian bytes. -/
def writeToArray32 (x : Nat) : List Nat := beBytes 32 x

/-- The most significant byte comes first. -/
example : (writeToArray32 (2 ^ 255)).head? = some 128 := by decide

end Fv256.Spec
