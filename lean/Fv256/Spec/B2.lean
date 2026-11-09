import Fv256.Spec.Core

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.B

/-- `x / y`, and `0` when `y = 0` (the `uint256` convention). -/
def divSpec (x y : Nat) : Nat := if y = 0 then 0 else x / y

/-- `x % y`, and `0` when `y = 0`. -/
def modSpec (x y : Nat) : Nat := if y = 0 then 0 else x % y

/-- `SMod`: two's complement operands; the result has the sign of `x` and the magnitude `|x| mod |y|`
(`0` when `y = 0`). -/
def smodSpec (x y : Nat) : Nat :=
  if 2 ^ 255 ≤ x then Fv256.Spec.neg (modSpec (Fv256.Spec.abs x) (Fv256.Spec.abs y))
  else modSpec (Fv256.Spec.abs x) (Fv256.Spec.abs y)

/-- `SDiv`: two's complement operands; truncating signed division (`0` when `y = 0`). -/
def sdivSpec (x y : Nat) : Nat :=
  if (2 ^ 255 ≤ x ↔ 2 ^ 255 ≤ y) then divSpec (Fv256.Spec.abs x) (Fv256.Spec.abs y)
  else Fv256.Spec.neg (divSpec (Fv256.Spec.abs x) (Fv256.Spec.abs y))

end Fv256.B
