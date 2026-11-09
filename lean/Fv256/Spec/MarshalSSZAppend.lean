import Fv256.Spec.BigEndian

/-!
# `func (z *Int) MarshalSSZAppend(dst []byte) ([]byte, error)`

`z.MarshalSSZAppend(dst)` appends the 32-byte SSZ encoding of `z` (LITTLE-endian) to `dst` and returns the extended slice and a nil
error; it never fails. If `dst` has spare capacity (`len + 32 ≤ cap`) the bytes are written in place after `dst`'s last element and the
result shares `dst`'s array; otherwise `append` allocates a larger array, copies the old elements and appends. Either way the old `len`
elements are preserved and the new `len + 32` elements are `dst ++ marshalSSZAppend x`.
-/

namespace Fv256.Spec

/-- The 32 bytes `z.MarshalSSZAppend(dst)` appends after the existing elements of `dst`, for the number `x` held in `z`: `x` in 32
little-endian bytes. -/
def marshalSSZAppend (x : Nat) : List Nat := leBytes 32 x

/-- The appended bytes of one: `01 00 … 00`. -/
example : marshalSSZAppend 1 = 1 :: List.replicate 31 0 := by decide

/-- Always 32 bytes. -/
example : (marshalSSZAppend 7).length = 32 := by decide

end Fv256.Spec
