/-!
# Two's-complement reading of a 256-bit number (shared by `Slt`, `Sgt`, `Sign` and the signed arithmetic)

A `uint256.Int` is stored as an unsigned number below `2^256`; the signed functions read it in two's complement:
numbers with the top bit (bit 255) set are negative.
-/

namespace Fv256.Spec

/-- The signed integer a 256-bit number stands for: itself when below `2^255`, otherwise itself minus `2^256`. -/
def signed (x : Nat) : Int := if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256

/-- All ones is `-1`. -/
example : signed (2 ^ 256 - 1) = -1 := by decide

/-- The smallest pattern with the top bit set is `-2^255`. -/
example : signed (2 ^ 255) = -(2 ^ 255) := by decide

example : signed 5 = 5 := by decide

end Fv256.Spec
