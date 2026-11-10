import Fv256.Spec.FromHex

/-!
# `func MustFromHex(hex string) *Int`

`MustFromHex(s)` is `FromHex(s)` that panics instead of returning an error: if `s` is valid it returns a new `Int` holding the
number, otherwise it panics with the error `FromHex(s)` would have returned.
-/

namespace Fv256.Spec

/-- Outcome of `MustFromHex(s)`: `ok v` means "returns a new `Int` holding `v`", `error e` means "panics with the error `e`". -/
def mustFromHex (s : List Nat) : HexResult := fromHex s

example : mustFromHex [48, 120, 49] = .ok 1 := by rfl
example : mustFromHex [49] = .error .missingPrefix := by rfl

end Fv256.Spec
