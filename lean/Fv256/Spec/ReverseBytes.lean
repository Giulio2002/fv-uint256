/-!
# `func (z *Int) ReverseBytes(x *Int) *Int`

`z.ReverseBytes(x)` sets `z` to `x` with its 32 bytes in reverse order (the byte-swap of the whole 256-bit word) and returns `z`:
byte `i` of `x` (counted from the least significant end) becomes byte `31 - i` of `z`. Reversing twice gives the original. There is no
error or panic case.
-/

namespace Fv256.Spec

/-- The number whose `n` bytes, from the most significant down, are the `n` lowest bytes of `x` taken from the lowest upwards
(so the lowest byte of `x` ends up on top). Helper for `reverseBytes`. -/
def reverseLow (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => x % 256 * 256 ^ n + reverseLow (x / 256) n

/-- Value of `z.ReverseBytes(x)`: the 32 bytes of `x` in reverse order. -/
def reverseBytes (x : Nat) : Nat := reverseLow x 32

/-- A one-byte value moves to the top byte. -/
example : reverseBytes 1 = 2 ^ 248 := by decide

/-- The top byte moves down to the bottom. -/
example : reverseBytes (2 ^ 248) = 1 := by decide

/-- Bytes `0x0102` (low byte `0x02`) become `0x02` on top and `0x01` just below. -/
example : reverseBytes 0x0102 = 0x02 * 2 ^ 248 + 0x01 * 2 ^ 240 := by decide

/-- Reversing twice is the identity (spot check). -/
example : reverseBytes (reverseBytes 0x0123456789abcdef) = 0x0123456789abcdef := by decide

end Fv256.Spec
