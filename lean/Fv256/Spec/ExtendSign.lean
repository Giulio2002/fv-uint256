/-!
# `func (z *Int) ExtendSign(x, byteNum *Int) *Int`

`z.ExtendSign(x, b)` sign-extends `x` from the byte numbered `b` (byte `0` is the least significant) and returns `z`: it keeps the low
`8(b+1)` bits of `x`, and fills every higher bit with a copy of bit `8b + 7` (the sign bit of that low part). When `b ≥ 31` the low part
is the whole word, so `z = x`. There is no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.ExtendSign(x, b)`: for `b < 31`, the low `8b + 8` bits of `x`, topped up with ones (`2^256 - 2^(8b+8)`) when bit `8b + 7`
of `x` is set and with zeros otherwise; `x` itself when `b ≥ 31`. -/
def extendSign (x b : Nat) : Nat :=
  if b < 31 then
    (if x / 2 ^ (8 * b + 7) % 2 = 1 then x % 2 ^ (8 * b + 8) + (2 ^ 256 - 2 ^ (8 * b + 8)) else x % 2 ^ (8 * b + 8))
  else x

/-- Byte 0 of `0x80` has its top bit set: the result is `0xff..80`. -/
example : extendSign 0x80 0 = 2 ^ 256 - 128 := by decide

/-- Byte 0 of `0x7f` has its top bit clear: unchanged. -/
example : extendSign 0x7f 0 = 0x7f := by decide

/-- Higher garbage above the chosen byte is discarded when the sign bit is clear. -/
example : extendSign 0x1_7f 0 = 0x7f := by decide

/-- From byte 31 on the word is unchanged. -/
example : extendSign (2 ^ 255 + 1) 31 = 2 ^ 255 + 1 := by decide

end Fv256.Spec
