import Fv256.Spec.SetFromBig

/-!
# `func MustFromBig(b *big.Int) *Int`

`uint256.MustFromBig(b)` returns a new `Int` holding `b mod 2^256` when `b` has at most four 64-bit limbs, and PANICS
(`panic("overflow")`) when it has more. For a nil `b` it returns nil and does not panic.
-/

namespace Fv256.Spec

/-- What `MustFromBig(b)` does for a non-nil `b` with integer value `b` and `limbs` limbs: `some v` (a new `Int` holding `v`) when it
returns, `none` when it panics. -/
def mustFromBig (b : Int) (limbs : Nat) : Option Nat :=
  if setFromBigOverflow limbs then none else some (setFromBig b)

/-- No overflow: the value. -/
example : mustFromBig (-1) 1 = some (2 ^ 256 - 1) := by decide

/-- Five limbs: panic. -/
example : mustFromBig 3 5 = none := by decide

end Fv256.Spec
