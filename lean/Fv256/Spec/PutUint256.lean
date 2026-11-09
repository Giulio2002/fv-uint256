import Fv256.Spec.BigEndian

/-!
# `func (z *Int) PutUint256(dest []byte)`

`z.PutUint256(dest)` writes all 32 bytes of `z`, big-endian (leading zero bytes included), into `dest[0:32]`; bytes of `dest`
beyond index 31 are left untouched. If `len(dest) < 32` the call PANICS (index out of range, from `_ = dest[31]`); the claim
covers the non-panicking calls only (`32 ≤ len(dest)`).
-/

namespace Fv256.Spec

/-- The bytes `dest[0:32]` holds after `z.PutUint256(dest)` (when `len(dest) ≥ 32`), for the number `x` held in `z`:
`x` in 32 big-endian bytes. -/
def putUint256 (x : Nat) : List Nat := beBytes 32 x

/-- The last byte is the lowest. -/
example : (putUint256 258).getLast? = some 2 := by decide

end Fv256.Spec
