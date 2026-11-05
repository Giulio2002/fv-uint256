import Fv256.Spec
import Fv256.SpecC

/-!
Sanity checks of the specification on small and boundary values (decided by the kernel). They are not part of any
correctness theorem; they document what the definitions in `Fv256.Spec` mean.
-/

namespace Fv256.Spec

example : add (W - 1) 1 = 0 := by decide
example : sub 0 1 = W - 1 := by decide
example : mul (2 ^ 128) (2 ^ 128) = 0 := by decide
example : neg 1 = W - 1 := by decide
example : not 0 = W - 1 := by decide
example : lt 1 2 = true := by decide
example : gt 1 2 = false := by decide
example : cmp 1 2 = -1 := by decide
example : cmp 2 2 = 0 := by decide
example : cmp 3 2 = 1 := by decide
example : slt (W - 1) 0 = true := by decide
example : sgt (W - 1) 0 = false := by decide
example : sign (W - 1) = -1 := by decide
example : sign 0 = 0 := by decide
example : abs (W - 5) = 5 := by decide
example : bitLen 0 = 0 := by decide
example : bitLen 1 = 1 := by decide
example : bitLen 255 = 8 := by decide
example : bitLen 256 = 9 := by decide
example : byteLen 256 = 2 := by decide
example : byte 31 0x1234 = 0x34 := by decide
example : byte 30 0x1234 = 0x12 := by decide
example : byte 32 0x1234 = 0 := by decide
example : lsh 1 255 = 2 ^ 255 := by decide
example : lsh 1 256 = 0 := by decide
example : rsh (2 ^ 255) 255 = 1 := by decide
example : rsh 5 256 = 0 := by decide
example : fromBE (fun i => [1, 2, 3].getD i 0) 3 = 0x010203 := by decide
example : setU 5 = 5 := by decide
example : sizeSSZ = 32 := by decide
example : addOv (W - 1) 1 = true := by decide
example : subOv 0 1 = true := by decide
example : mulOv (2 ^ 128) (2 ^ 128) = true := by decide
example : uint64Ov (2 ^ 64) = true := by decide
example : uint64 (2 ^ 64 + 7) = 7 := by decide

/-! `FromBig` / `MustFromBig` / `SetFromBig` on NEGATIVE big.Ints: two's complement wrapping, no overflow flag
(the flag only looks at the number of words), so `FromBig(-1) = 2^256 - 1` with `overflow = false`. -/
example : Fv256.C.fromBig true 1 = W - 1 := by decide
example : Fv256.C.fromBigOv 1 = false := by decide
example : Fv256.C.fromBig true 0 = 0 := by decide
example : Fv256.C.fromBig true (2 ^ 256 - 1) = 1 := by decide
example : Fv256.C.fromBigOv 5 = true := by decide

end Fv256.Spec
