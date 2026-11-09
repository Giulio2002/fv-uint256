/-!
# `func (z *Int) Not(x *Int) *Int`

`z.Not(x)` sets `z` to the bitwise complement of `x` (every one of the 256 bits flipped), i.e. `2^256 - 1 - x`, and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Not(x)` for a 256-bit `x`: the bitwise complement, `2^256 - 1 - x`. -/
def not (x : Nat) : Nat := 2 ^ 256 - 1 - x

/-- Complementing zero gives all ones. -/
example : not 0 = 2 ^ 256 - 1 := by decide

/-- Complementing all ones gives zero. -/
example : not (2 ^ 256 - 1) = 0 := by decide

end Fv256.Spec
