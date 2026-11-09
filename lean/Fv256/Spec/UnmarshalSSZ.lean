import Fv256.Spec.BigEndian

/-!
# `func (z *Int) UnmarshalSSZ(buf []byte) error`

`z.UnmarshalSSZ(buf)` decodes a 32-byte LITTLE-endian SSZ encoding. If `len(buf) = 32` it sets `z` to the number whose little-endian
bytes are `buf` and returns nil; otherwise it leaves `z` unchanged and returns an error wrapping `ErrBadEncodedLength` with the
message `"bad ssz encoded length: have <len>, want 32 bytes"` (`fmt.Errorf("%w: have %d, want %d bytes", …)`).
-/

namespace Fv256.Spec

/-- The number whose little-endian bytes are `bs` (least significant byte first). -/
def leValue : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * leValue bs

/-- The number `z` holds after `z.UnmarshalSSZ(buf)` when it succeeds (`len(buf) = 32`), for the bytes `buf`; `none` when the length is
wrong (the call returns `ErrBadEncodedLength`). -/
def unmarshalSSZ (buf : List Nat) : Option Nat := if buf.length = 32 then some (leValue buf) else none

/-- Little-endian: the first byte is the least significant. -/
example : leValue [1, 2] = 513 := by decide

/-- One is `01 00 … 00`. -/
example : unmarshalSSZ (1 :: List.replicate 31 0) = some 1 := by decide

/-- A wrong length is an error. -/
example : unmarshalSSZ [1, 2, 3] = none := by decide

end Fv256.Spec
