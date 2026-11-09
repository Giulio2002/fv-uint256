import Fv256.Spec.SetFromBig

/-!
# `func FromBig(b *big.Int) (*Int, bool)`

`uint256.FromBig(b)` returns a new `Int` holding `b mod 2^256` together with the overflow flag of `SetFromBig` (`true` iff the
magnitude of `b` has more than four 64-bit limbs). For a nil `b` it returns `(nil, false)`. No panic.
-/

namespace Fv256.Spec

/-- The pair `FromBig(b)` returns for a non-nil `b` with integer value `b` and `limbs` limbs: the number held by the new `Int`, and
the overflow flag. (A nil `b` returns the nil pointer and `false`.) -/
def fromBig (b : Int) (limbs : Nat) : Nat × Bool := (setFromBig b, setFromBigOverflow limbs)

/-- Five limbs overflow; the value is still reduced modulo `2^256`. -/
example : fromBig (2 ^ 256 + 3) 5 = (3, true) := by decide

/-- Four limbs do not overflow. -/
example : fromBig 12 1 = (12, false) := by decide

end Fv256.Spec
