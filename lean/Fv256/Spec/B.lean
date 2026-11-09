import Janus
import Fv256.Spec.Core

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.B

/-- The DOCUMENTED behaviour of `Float64` ("the float64 value nearest to x"): IEEE round-to-nearest-even of the exact
natural number `x`, as the bit pattern (`Janus.Float.fromInt`, IEEE `convertFromInt`). The library does NOT meet this
for `x >= 2^64` (it truncates, see `float64BitsTrunc` and `Fv256.B.float64_trunc_not_nearest`). -/
def float64BitsNearest (x : Nat) : Nat := Janus.Float.fromInt Janus.Float.binary64 .rne x

end Fv256.B
