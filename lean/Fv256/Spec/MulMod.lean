/-!
# `func (z *Int) MulMod(x, y, m *Int) *Int`

`z.MulMod(x, y, m)` sets `z = (x * y) mod m` and returns `z`. The product is computed WITHOUT wrap-around (a 512-bit product is
fine), so the result is the true remainder. A zero modulus is not an error: the result is `0`. No call panics.
-/

namespace Fv256.Spec

/-- Value of `z.MulMod(x, y, m)`: `0` when `m = 0`, otherwise the remainder of the exact product `x * y` modulo `m`. -/
def mulMod (x y m : Nat) : Nat := if m = 0 then 0 else (x * y) % m

/-- Small numbers: `(5 * 4) mod 7 = 6`. -/
example : mulMod 5 4 7 = 6 := by decide

/-- A zero modulus gives zero. -/
example : mulMod 5 4 0 = 0 := by decide

/-- No truncation of the intermediate product: `(2^256 - 1)^2 = 1 (mod 2^256 - 2)`, although the product exceeds `2^256`. -/
example : mulMod (2 ^ 256 - 1) (2 ^ 256 - 1) (2 ^ 256 - 2) = 1 := by decide

end Fv256.Spec
