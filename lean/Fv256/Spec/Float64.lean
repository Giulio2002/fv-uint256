/-!
# `func (z *Int) Float64() float64`

`z.Float64()` converts the 256-bit number `z` to a `float64`: the result is the `float64` nearest to the number, with ties going to the
even significand (IEEE 754 round-to-nearest-even, as for `float64(n)` of an integer). Numbers below `2^53` convert exactly; larger ones
are rounded to 53 significant bits (a rounding carry can bump the exponent). No 256-bit number overflows `float64`
(the largest is below `2^256`, far below `2^1024`), so the result is always finite, and `0` converts to `+0`.
There is no error or panic case. Specified here as the 64 bits of the IEEE binary64 encoding (sign `0`, 11 exponent bits biased by 1023,
52 fraction bits).
-/

namespace Fv256.Spec

/-- The 64-bit IEEE 754 encoding of the `float64` nearest to the natural number `x < 2^256` (ties to even). `x = 0` is `+0`. With
`e = ⌊log₂ x⌋`: if `e ≤ 52` the number is exact and only needs the leading bit dropped; otherwise the low `e - 52` bits are rounded away
(up when the dropped part exceeds half, or equals half and the kept part is odd), and when that rounding carries out to `2^53` the
exponent goes up by one with a zero fraction. The exponent field is `e + 1023` (`+ 1` after a carry), the fraction the kept bits below the
leading one. -/
def float64Bits (x : Nat) : Nat :=
  if x = 0 then 0 else
  let e := Nat.log2 x
  if e ≤ 52 then (e + 1023) * 2 ^ 52 + x * 2 ^ (52 - e) % 2 ^ 52
  else
    let kept := x / 2 ^ (e - 52)
    let dropped := x % 2 ^ (e - 52)
    let up := dropped * 2 > 2 ^ (e - 52) ∨ (dropped * 2 = 2 ^ (e - 52) ∧ kept % 2 = 1)
    let rounded := if up then kept + 1 else kept
    if rounded = 2 ^ 53 then (e + 1 + 1023) * 2 ^ 52 else (e + 1023) * 2 ^ 52 + rounded % 2 ^ 52

/-- `0` is `+0.0`. -/
example : float64Bits 0 = 0 := by decide

/-- `1.0 = 0x3FF0000000000000`. -/
example : float64Bits 1 = 0x3FF0000000000000 := by decide

/-- `2.0 = 0x4000000000000000`. -/
example : float64Bits 2 = 0x4000000000000000 := by decide

/-- `3.0 = 0x4008000000000000`. -/
example : float64Bits 3 = 0x4008000000000000 := by decide

/-- `2^53 + 1` is a tie between `2^53` and `2^53 + 2`: it rounds to the even significand `2^53` (`9007199254740992.0`). -/
example : float64Bits (2 ^ 53 + 1) = float64Bits (2 ^ 53) := by decide

/-- `2^53 + 3` is a tie that rounds up to `2^53 + 4`. -/
example : float64Bits (2 ^ 53 + 3) = float64Bits (2 ^ 53 + 4) := by decide

/-- The largest word rounds up to `2^256`, whose exponent field is `256 + 1023 = 1279`. -/
example : float64Bits (2 ^ 256 - 1) = 1279 * 2 ^ 52 := by decide

end Fv256.Spec
