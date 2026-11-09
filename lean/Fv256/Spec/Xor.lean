/-!
# `func (z *Int) Xor(x, y *Int) *Int`

`z.Xor(x, y)` sets `z` to the bitwise exclusive OR of `x` and `y` and returns `z`. No error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Xor(x, y)`: bit `i` of the result is set exactly when bit `i` is set in exactly one of `x`, `y`. -/
def xor (x y : Nat) : Nat := x ^^^ y

/-- 12 XOR 10 = 6. -/
example : xor 12 10 = 6 := by decide

/-- A number XOR itself is zero. -/
example : xor 12 12 = 0 := by decide

end Fv256.Spec
