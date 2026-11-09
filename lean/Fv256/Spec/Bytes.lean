import Fv256.Spec.BigEndian

/-!
# `func (z *Int) Bytes() []byte`

`z.Bytes()` returns the minimal big-endian encoding of `z` as a slice: no leading zero byte, and the EMPTY slice for `z = 0`.
Its length is `ByteLen(z)`. No error or panic case.
-/

namespace Fv256.Spec

/-- The number of bytes in the minimal big-endian encoding of `x`: `0` for `x = 0`, otherwise `⌊log₂ x / 8⌋ + 1`
(so `1 ≤ x < 256` is one byte, `256 ≤ x < 65536` two bytes, and so on). -/
def minBytes (x : Nat) : Nat := if x = 0 then 0 else x.log2 / 8 + 1

/-- The contents of the slice `z.Bytes()` for the number `x` held in `z`: `x` in exactly `minBytes x` big-endian bytes. -/
def bytes (x : Nat) : List Nat := beBytes (minBytes x) x

/-- Zero is the empty slice. -/
example : bytes 0 = [] := by decide

/-- No leading zero byte. -/
example : bytes 255 = [255] := by decide

/-- One more bit needs a second byte. -/
example : bytes 256 = [1, 0] := by decide

end Fv256.Spec
