/-!
# `func (z *Int) IntoBig(b **big.Int)`

`z.IntoBig(b)` stores in `*b` a `*big.Int` whose integer value is the (non-negative) number `z` holds, reusing the `big.Int` that `*b`
already points to when it can and allocating a new one otherwise; for a nil receiver it stores nil in `*b`. It does not modify `z` and cannot fail.
-/

namespace Fv256.Spec

/-- The integer value of the `big.Int` that `z.IntoBig(b)` leaves in `*b` for the number `x` held in `z`: `x` itself, never negative
(a nil `z` stores nil instead). -/
def intoBig (x : Nat) : Int := x

/-- The value is non-negative. -/
example : 0 ≤ intoBig 5 := by decide

/-- The largest word keeps its value (no wrap-around). -/
example : intoBig (2 ^ 256 - 1) = 2 ^ 256 - 1 := by decide

end Fv256.Spec
