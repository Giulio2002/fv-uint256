import Fv256.Spec.Dec

/-!
# `func (z *Int) MarshalJSON() ([]byte, error)`

`z.MarshalJSON()` returns the decimal representation of `z` wrapped in double quotes (a JSON string, so that large numbers survive
JSON consumers that use floating point) and a `nil` error. It never fails and never panics.
-/

namespace Fv256.Spec

/-- The bytes of the slice returned by `z.MarshalJSON()`: a double quote (34), the decimal digits of `z`, a double quote. -/
def marshalJSON (x : Nat) : List Nat := 34 :: (dec x ++ [34])

example : marshalJSON 12 = [34, 49, 50, 34] := by decide

end Fv256.Spec
