import Fv256.Spec

/-!
# Specifications of the division family (family B, part 2)

All numbers are naturals below `2^256`; Go's `uint256` operations define division and remainder by zero as `0`.
-/

namespace Fv256.B

/-- `x / y`, and `0` when `y = 0` (the `uint256` convention). -/
def divSpec (x y : Nat) : Nat := if y = 0 then 0 else x / y

/-- `x % y`, and `0` when `y = 0`. -/
def modSpec (x y : Nat) : Nat := if y = 0 then 0 else x % y

end Fv256.B
