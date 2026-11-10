import Fv256.Spec.Mod
import Fv256.Spec.SDiv

/-!
# `func (z *Int) SMod(x, y *Int) *Int`

`z.SMod(x, y)` reads `x` and `y` as two's complement signed 256-bit integers (a word `>= 2^255` is negative) and sets `z` to
`sign(x) * (|x| mod |y|)`: the remainder has the magnitude `|x| mod |y|` and the sign of the dividend `x` (the sign of `y` is
ignored). The result is stored as a two's complement word. A zero `y` is NOT an error and does not panic: the result is `0`.
-/

namespace Fv256.Spec

/-- Value of `z.SMod(x, y)`: the unsigned remainder of the magnitudes (`0` when `y = 0`), negated when `x` is negative. -/
def smod (x y : Nat) : Nat :=
  if 2 ^ 255 ≤ x then negate (mod (magnitude x) (magnitude y))
  else mod (magnitude x) (magnitude y)

/-- `-7 mod 3 = -1` (the sign follows the dividend). -/
example : smod (2 ^ 256 - 7) 3 = 2 ^ 256 - 1 := by decide

/-- `7 mod -3 = 1` (the sign of the modulus is ignored). -/
example : smod 7 (2 ^ 256 - 3) = 1 := by decide

/-- A zero modulus gives zero. -/
example : smod (2 ^ 256 - 7) 0 = 0 := by decide

end Fv256.Spec
