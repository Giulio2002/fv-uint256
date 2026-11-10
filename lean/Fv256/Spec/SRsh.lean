/-!
# `func (z *Int) SRsh(x *Int, n uint) *Int`

`z.SRsh(x, n)` sets `z` to the arithmetic (sign-preserving) right shift of `x` by `n` bits, reading `x` as a 256-bit two's-complement
number (negative when `x ≥ 2^255`), and returns `z`. A non-negative `x` shifts like `Rsh`; a negative `x` shifts with ones entering at
the top, i.e. `⌊x_signed / 2^n⌋` rounded towards minus infinity (so a shift by `256` or more gives `0` for non-negative `x` and
`2^256 - 1`, i.e. `-1`, for negative `x`). There is no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.SRsh(x, n)`: for `x < 2^255` it is `x / 2^n`; otherwise it is the bitwise complement of the shift of the complement,
`(2^256 - 1) - ((2^256 - 1 - x) / 2^n)` (ones shifted in at the top). -/
def srsh (x n : Nat) : Nat := if x < 2 ^ 255 then x / 2 ^ n else 2 ^ 256 - 1 - (2 ^ 256 - 1 - x) / 2 ^ n

/-- A positive number shifts like `Rsh`. -/
example : srsh 8 2 = 2 := by decide

/-- `-8` (as `2^256 - 8`) shifted right by 2 is `-2`. -/
example : srsh (2 ^ 256 - 8) 2 = 2 ^ 256 - 2 := by decide

/-- A negative number shifted far enough is `-1`. -/
example : srsh (2 ^ 256 - 8) 300 = 2 ^ 256 - 1 := by decide

end Fv256.Spec
