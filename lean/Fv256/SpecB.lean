import Janus
import Fv256.Spec

/-!
# Specification, family B: division, modular arithmetic and iterative numerics

Plain mathematics on `Nat`, written without reference to the Go code or to any machine
(see `Fv256.Spec` for the conventions: a `uint256.Int` denotes a number `x < 2^256`).
-/

namespace Fv256.B

/-- The IEEE 754 binary64 bit pattern that `x.Float64()` returns for the number `x < 2^256`.
Below `2^64` the number is converted with round-to-nearest-even (`Janus.Float.fromInt`, IEEE
`convertFromInt`). From `2^64` on the library truncates: with `n = bitLen x`, the exponent field is
`n - 1 + 1023` and the fraction field holds the 52 bits that follow the leading one (rounding
toward zero, no sticky bit). -/
def float64BitsTrunc (x : Nat) : Nat :=
  if x < 2 ^ 64 then Janus.Float.fromInt Janus.Float.binary64 .rne x
  else (Fv256.Spec.bitLen x + 1022) * 2 ^ 52 + x / 2 ^ (Fv256.Spec.bitLen x - 53) % 2 ^ 52

/-- The DOCUMENTED behaviour of `Float64` ("the float64 value nearest to x"): IEEE round-to-nearest-even of the exact
natural number `x`, as the bit pattern (`Janus.Float.fromInt`, IEEE `convertFromInt`). The library does NOT meet this
for `x >= 2^64` (it truncates, see `float64BitsTrunc` and `Fv256.B.float64_trunc_not_nearest`). -/
def float64BitsNearest (x : Nat) : Nat := Janus.Float.fromInt Janus.Float.binary64 .rne x

/-- Finding F-B1 (doc mismatch): at `x = 2^64 + 4095` the library's (truncating) result differs from the documented
nearest-even result. -/
theorem float64_trunc_not_nearest : float64BitsTrunc (2 ^ 64 + 4095) ≠ float64BitsNearest (2 ^ 64 + 4095) := by
  decide

end Fv256.B
