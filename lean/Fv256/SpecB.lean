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
def float64Bits (x : Nat) : Nat :=
  if x < 2 ^ 64 then Janus.Float.fromInt Janus.Float.binary64 .rne x
  else (Fv256.Spec.bitLen x + 1022) * 2 ^ 52 + x / 2 ^ (Fv256.Spec.bitLen x - 53) % 2 ^ 52

end Fv256.B
