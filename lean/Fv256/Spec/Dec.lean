/-!
# `func (z *Int) Dec() string`

`z.Dec()` returns the decimal representation of `z`: the base-10 digits of the number, most significant first, without leading
zeros (`0` is `"0"`), no sign and no separator. It never fails and never panics. Strings are modelled as lists of ASCII byte values.
-/

namespace Fv256.Spec

/-- The ASCII bytes of the decimal representation of `x` (digits `'0'..'9'`, most significant first, no leading zero). -/
def dec (x : Nat) : List Nat := (Nat.toDigits 10 x).map Char.toNat

example : dec 0 = [48] := by decide
example : dec 1234 = [49, 50, 51, 52] := by decide
example : dec 100 = [49, 48, 48] := by decide

end Fv256.Spec
