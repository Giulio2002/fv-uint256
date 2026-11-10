import Fv256.Spec.Dec

/-!
# `func (z *Int) MarshalText() ([]byte, error)`

`z.MarshalText()` returns the decimal representation of `z` as a byte slice (the same bytes as `z.Dec()`) and a `nil` error.
It never fails and never panics.
-/

namespace Fv256.Spec

/-- The bytes of the slice returned by `z.MarshalText()`: the decimal digits of `z`. -/
def marshalText (x : Nat) : List Nat := dec x

example : marshalText 7 = [55] := by decide

end Fv256.Spec
