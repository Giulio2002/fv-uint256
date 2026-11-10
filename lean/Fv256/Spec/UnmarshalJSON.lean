import Fv256.Spec.UnmarshalText

/-!
# `func (z *Int) UnmarshalJSON(input []byte) error`

`z.UnmarshalJSON(input)` accepts a JSON string or a bare JSON number.
* If `input` is quoted (at least two bytes, first and last byte `"`), the text between the quotes is parsed exactly like
  `UnmarshalText` (hexadecimal with a `0x`/`0X` prefix, decimal otherwise); `"0xff"` and `"255"` are both `255`.
* Otherwise the whole input is parsed as a decimal number like `SetFromDecimal` (`255` is `255`; `0xff` without quotes is a syntax error).
On success `z` holds the number and `err = nil`.
-/

namespace Fv256.Spec

/-- The input is a quoted string: at least two bytes, the first and the last one a double quote (byte 34). -/
def isQuoted (s : List Nat) : Bool := 2 ≤ s.length && s.head? == some 34 && s.getLast? == some 34

/-- THE SPECIFICATION of `UnmarshalJSON`: a quoted input is parsed as text without its quotes; anything else as a decimal. -/
def unmarshalJSON (s : List Nat) : TextResult :=
  if isQuoted s then unmarshalText (s.drop 1).dropLast else .ofDec (setFromDecimal s)

example : unmarshalJSON [34, 50, 53, 53, 34] = .ok 255 := by decide
example : unmarshalJSON [34, 48, 120, 102, 102, 34] = .ok 255 := by decide
example : unmarshalJSON [50, 53, 53] = .ok 255 := by decide
example : unmarshalJSON [48, 120, 102, 102] = .decSyntax 1 3 := by decide
example : unmarshalJSON [34] = .decSyntax 0 1 := by decide
example : unmarshalJSON [34, 34] = .decEof := by decide

end Fv256.Spec
