import Fv256.Spec.BigEndian

/-!
# `func (z *Int) Bytes20() [20]byte`

`z.Bytes20()` returns the LOW 20 bytes of `z` as a big-endian array (the address-sized suffix): the number
`z mod 2^160`, most significant byte first. The upper 12 bytes of `z` are dropped silently. No error or panic case.
-/

namespace Fv256.Spec

/-- The 20 bytes of `z.Bytes20()` for the number `x` held in `z`: `x mod 2^160` in 20 big-endian bytes. -/
def bytes20 (x : Nat) : List Nat := beBytes 20 x

/-- Bytes above the low 160 bits are dropped: `2^160 + 1` and `1` give the same array. -/
example : bytes20 (2 ^ 160 + 1) = bytes20 1 := by decide

/-- The array always has 20 bytes. -/
example : (bytes20 12345).length = 20 := by decide

end Fv256.Spec
