import Fv256.Spec
import Fv256.RecipSpec

/-!
# Specifications of the modular-arithmetic and power family (FV-F)

Numbers are naturals below `2^256`.  Documented conventions of `uint256` (Go doc comments on master 48f3f44):
`AddMod`, `MulMod`, `MulModWithReciprocal`: "If m == 0, z is set to 0 (OBS: differs from the big.Int)";
`MulDivOverflow`: `(x*y)/d` with full precision, `z` is the low 256 bits of the quotient and the flag says the quotient
does not fit; a zero `d` gives `(0, false)`; `Exp`: `base**exponent mod 2**256`; `Sqrt`: `⌊√x⌋`;
`Reciprocal`: "a 320-bit value representing 1/m", only for `2^192 ≤ m < 2^256` (zero otherwise).
-/

namespace Fv256.F

/-- `z.AddMod(x, y, m)`: `(x + y) mod m`, and `0` when `m = 0`. -/
def addmodSpec (x y m : Nat) : Nat := if m = 0 then 0 else (x + y) % m

/-- `z.MulMod(x, y, m)`: `(x * y) mod m`, and `0` when `m = 0`. -/
def mulmodSpec (x y m : Nat) : Nat := if m = 0 then 0 else (x * y) % m

/-- `z.MulDivOverflow(x, y, d)` value: low 256 bits of `(x*y)/d`, `0` when `d = 0`. -/
def muldivSpec (x y d : Nat) : Nat := if d = 0 then 0 else (x * y / d) % 2 ^ 256

/-- `z.MulDivOverflow(x, y, d)` flag: the quotient `(x*y)/d` does not fit in 256 bits (`false` when `d = 0`). -/
def muldivOv (x y d : Nat) : Bool := if d = 0 then false else decide (2 ^ 256 ≤ x * y / d)

/-- `z.Exp(base, exponent)`: `base ^ exponent mod 2^256`. -/
def expSpec (b e : Nat) : Nat := b ^ e % 2 ^ 256

/-- `z.Sqrt(x)` is `z` iff `z` is the integer square root: `z² ≤ x < (z+1)²`. -/
def IsSqrt (x z : Nat) : Prop := z * z ≤ x ∧ x < (z + 1) * (z + 1)

end Fv256.F
