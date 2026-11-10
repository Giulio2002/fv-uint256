import Fv256.Spec.BigEndian

/-!
# `func (z *Int) WriteToArray20(dest *[20]byte)`

`z.WriteToArray20(dest)` overwrites the 20 bytes of `*dest` with the LOW 20 bytes of `z` in BIG-endian order (the number
`z mod 2^160`); the upper 12 bytes of `z` are dropped. Nothing else is written. No error or panic case.
-/

namespace Fv256.Spec

/-- The 20 bytes `*dest` holds after `z.WriteToArray20(dest)`, for the number `x` held in `z`: `x mod 2^160` in 20 big-endian bytes. -/
def writeToArray20 (x : Nat) : List Nat := beBytes 20 x

/-- Only the low 20 bytes are written. -/
example : writeToArray20 (2 ^ 160 + 7) = writeToArray20 7 := by decide

end Fv256.Spec
