import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.RecipSpec
import Fv256.Spec.F

/-!
# Specifications of the modular-arithmetic and power family (FV-F)

Numbers are naturals below `2^256`.  Documented conventions of `uint256` (Go doc comments on master 48f3f44):
`AddMod`, `MulMod`, `MulModWithReciprocal`: "If m == 0, z is set to 0 (OBS: differs from the big.Int)";
`MulDivOverflow`: `(x*y)/d` with full precision, `z` is the low 256 bits of the quotient and the flag says the quotient
does not fit; a zero `d` gives `(0, false)`; `Exp`: `base**exponent mod 2**256`; `Sqrt`: `⌊√x⌋`;
`Reciprocal`: "a 320-bit value representing 1/m", only for `2^192 ≤ m < 2^256` (zero otherwise).
-/

namespace Fv256.F

end Fv256.F
