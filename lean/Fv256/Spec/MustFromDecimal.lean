import Fv256.Spec.FromDecimal

/-!
# `func MustFromDecimal(decimal string) *Int`

`MustFromDecimal(s)` is `FromDecimal(s)` that panics instead of returning an error: if `s` is valid it returns a new `Int` holding
the number, otherwise it panics with the error `FromDecimal(s)` would have returned.
-/

namespace Fv256.Spec

/-- Outcome of `MustFromDecimal(s)`: `ok v` means "returns a new `Int` holding `v`"; `eof`, `range`, `badSyntax _ _` mean "panics with
that error". -/
def mustFromDecimal (s : List Nat) : DecResult := fromDecimal s

example : mustFromDecimal [55] = .ok 7 := by decide
example : mustFromDecimal [] = .eof := by decide

end Fv256.Spec
