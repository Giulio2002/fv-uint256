import Fv256.Spec.BigEndian

/-!
# `func (z *Int) WriteToSlice(dest []byte)`

`z.WriteToSlice(dest)` writes `z` big-endian into the start of `dest`, using at most 32 bytes.
* `len(dest) ≥ 32`: the full 32-byte encoding fills `dest[0:32]`; the rest of `dest` is left untouched.
* `len(dest) < 32`: only the LOW `len(dest)` bytes of `z` are written (the number `z mod 256^len(dest)`), filling all of `dest`.
No error or panic case (an empty `dest` writes nothing).
-/

namespace Fv256.Spec

/-- The bytes `dest[0 : min len 32]` holds after `z.WriteToSlice(dest)` with `len(dest) = len`, for the number `x` held in `z`:
the low `min len 32` bytes of `x`, big-endian. -/
def writeToSlice (x len : Nat) : List Nat := beBytes (min len 32) x

/-- A short destination gets the low bytes. -/
example : writeToSlice 0x0102030405 3 = [3, 4, 5] := by decide

/-- A long destination gets exactly 32 bytes written. -/
example : (writeToSlice 7 100).length = 32 := by decide

/-- An empty destination writes nothing. -/
example : writeToSlice 7 0 = [] := by decide

end Fv256.Spec
