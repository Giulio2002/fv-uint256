import Fv256.Spec.SetFromHex

/-!
# `func FromHex(hex string) (*Int, error)`

`FromHex(s)` allocates a new `Int` and parses `s` into it exactly like `SetFromHex` (see `Fv256/Spec/SetFromHex.lean` for the
accepted syntax and the six errors). On success it returns `(z, nil)` with `z` holding the number; on any error it returns
`(nil, err)`.
-/

namespace Fv256.Spec

/-- Outcome of `FromHex(s)`: the number held by the returned `*Int`, or the error returned with a `nil` pointer. This is the outcome of
`SetFromHex` on the same string (`FromHex` adds only the allocation of the result). -/
def fromHex (s : List Nat) : HexResult := setFromHex s

example : fromHex [48, 120, 102, 102] = .ok 255 := by rfl
example : fromHex [48, 120] = .error .emptyNumber := by rfl

end Fv256.Spec
