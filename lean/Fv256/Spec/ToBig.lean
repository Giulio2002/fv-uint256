/-!
# `func (z *Int) ToBig() *big.Int`

`z.ToBig()` returns a new `*big.Int` whose integer value is the (non-negative) number `z` holds; for a nil receiver it returns nil.
It does not modify `z` and cannot fail.
-/

namespace Fv256.Spec

/-- The integer value of the `big.Int` that `z.ToBig()` returns for the number `x` held in `z`: `x` itself, never negative
(a nil `z` returns nil instead). -/
def toBig (x : Nat) : Int := x

/-- The value is non-negative. -/
example : 0 ≤ toBig 5 := by decide

/-- The largest word keeps its value (no wrap-around). -/
example : toBig (2 ^ 256 - 1) = 2 ^ 256 - 1 := by decide

end Fv256.Spec
