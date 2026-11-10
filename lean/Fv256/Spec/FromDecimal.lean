import Fv256.Spec.SetFromDecimal

/-!
# `func FromDecimal(decimal string) (*Int, error)`

`FromDecimal(s)` allocates a new `Int` and parses `s` into it exactly like `SetFromDecimal` (see `Fv256/Spec/SetFromDecimal.lean` for
the accepted syntax and the errors). On success it returns `(z, nil)` with `z` holding the number; on any error it returns `(nil, err)`.
-/

namespace Fv256.Spec

/-- Outcome of `FromDecimal(s)`: the number held by the returned `*Int`, or the error returned with a `nil` pointer. This is the
outcome of `SetFromDecimal` on the same string (`FromDecimal` adds only the allocation of the result). -/
def fromDecimal (s : List Nat) : DecResult := setFromDecimal s

example : fromDecimal [49, 50, 51] = .ok 123 := by decide
example : fromDecimal [] = .eof := by decide

end Fv256.Spec
