import Fv256.Spec.BigEndian

/-!
# `func (z *Int) HashTreeRoot() ([32]byte, error)`

`z.HashTreeRoot()` returns the SSZ hash tree root of a `uint256`. For a basic 256-bit type nothing is hashed: the root is the
value's 32-byte LITTLE-endian serialization (note: little-endian, unlike `Bytes32`), and the error is always `nil`.
-/

namespace Fv256.Spec

/-- The 32 bytes of the root `z.HashTreeRoot()` returns for the number `x` held in `z`: `x` in 32 little-endian bytes. -/
def hashTreeRoot (x : Nat) : List Nat := leBytes 32 x

/-- One is `01 00 00 ... 00`: the least significant byte comes first. -/
example : hashTreeRoot 1 = 1 :: List.replicate 31 0 := by decide

/-- The root has 32 bytes. -/
example : (hashTreeRoot 12345).length = 32 := by decide

end Fv256.Spec
