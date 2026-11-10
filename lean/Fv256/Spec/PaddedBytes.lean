import Fv256.Spec.BigEndian

/-!
# `func (z *Int) PaddedBytes(n int) []byte`

`z.PaddedBytes(n)` returns a fresh `n`-byte slice holding `z` big-endian, zero-padded in front when `n > 32` and keeping only
the LOW `n` bytes (the number `z mod 256^n`) when `n < 32`. A negative `n` panics in `make`; the claim covers `0 ≤ n ≤ 2^48`.
-/

namespace Fv256.Spec

/-- The contents of the slice returned by `z.PaddedBytes(n)`, for the number `x` held in `z`: `x mod 256^n` in `n` big-endian bytes. -/
def paddedBytes (x n : Nat) : List Nat := beBytes n x

/-- `1` padded to 20 bytes: nineteen zeros and a one. -/
example : paddedBytes 1 20 = List.replicate 19 0 ++ [1] := by decide

/-- A short length keeps the low bytes. -/
example : paddedBytes 0x0102 1 = [2] := by decide

end Fv256.Spec
