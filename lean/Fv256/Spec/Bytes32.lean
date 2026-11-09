import Fv256.Spec.BigEndian

/-!
# `func (z *Int) Bytes32() [32]byte`

`z.Bytes32()` returns the value of `z` as a 32-byte BIG-endian array: the most significant byte first, leading zero bytes
included. It has no error or panic case: every `z` is valid.
-/

namespace Fv256.Spec

/-- The 32 bytes of `z.Bytes32()` for the number `x` held in `z`: `x` in 32 big-endian bytes (always exact, as `x < 2^256`). -/
def bytes32 (x : Nat) : List Nat := beBytes 32 x

/-- One is the last byte. -/
example : (bytes32 1).getLast? = some 1 := by decide

/-- The array always has 32 bytes. -/
example : (bytes32 12345).length = 32 := by decide

end Fv256.Spec
