import Fv256.Spec.BigEndian

/-!
# `func (z *Int) MarshalSSZInto(dst []byte) ([]byte, error)`  (deprecated)

`z.MarshalSSZInto(dst)` writes the 32-byte SSZ encoding of `z` (LITTLE-endian) into `dst[0:32]` and returns `dst[32:]` and a nil error.
If `len(dst) < 32` it writes nothing and returns `(nil, err)` where `err` wraps `ErrBadBufferLength` with the message
`"bad ssz buffer length: have <len>, want 32 bytes"` (`fmt.Errorf("%w: have %d, want %d bytes", …)`). `dst` is never reallocated.
-/

namespace Fv256.Spec

/-- The 32 bytes `dst[0:32]` hold after a successful `z.MarshalSSZInto(dst)`, for the number `x` held in `z`: `x` in 32 little-endian
bytes. The call succeeds exactly when `32 ≤ len(dst)` (otherwise `dst` is left unchanged and the error described above is returned). -/
def marshalSSZInto (x : Nat) : List Nat := leBytes 32 x

/-- The call succeeds iff the destination has room for 32 bytes. -/
def marshalSSZIntoOk (dstLen : Nat) : Bool := decide (32 ≤ dstLen)

/-- One is `01 00 … 00`. -/
example : marshalSSZInto 1 = 1 :: List.replicate 31 0 := by decide

/-- Room for exactly 32 bytes is enough, 31 is not. -/
example : marshalSSZIntoOk 32 = true ∧ marshalSSZIntoOk 31 = false := by decide

end Fv256.Spec
