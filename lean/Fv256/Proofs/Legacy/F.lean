import Fv256.Proofs.Legacy.RecipSpec
import Fv256.Spec.Core

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


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

/-- precondition on the reciprocal argument of `MulModWithReciprocal(x, y, m, mu)`: when `m` has four words (`m[3] ≠ 0`, i.e. `2^192 ≤ m`),
`mu` is within the provable window `⌊(2^512-1)/m⌋ - 3 ≤ mu ≤ ⌊(2^512-1)/m⌋` (`RecipWeak`); for shorter `m` the argument is unused.
The documented result is `x * y mod m`, and `0` when `m = 0` (`mulmodSpec`), exactly. -/
def MuOK (m mu : Nat) : Prop := 2 ^ 192 ≤ m → RecipWeak m mu

end Fv256.F
