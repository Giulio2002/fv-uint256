import Fv256.Spec.SetFromHex
import Fv256.Spec.SetFromDecimal

/-!
# `func (z *Int) UnmarshalText(input []byte) error`

`z.UnmarshalText(input)` parses either a hexadecimal or a decimal number.
* If `input` starts with `"0x"` or `"0X"` it is parsed exactly like `SetFromHex` (see `Fv256/Spec/SetFromHex.lean`).
* Otherwise it is parsed exactly like `SetFromDecimal` (see `Fv256/Spec/SetFromDecimal.lean`).
On success `z` holds the number and `err = nil`; the errors are those of the parser that was chosen.
-/

namespace Fv256.Spec

/-- The outcome of parsing text that may be hexadecimal or decimal: the number, an error of the hex parser, or an error of the
decimal parser. A sum of core types (`Nat ⊕ HexError ⊕ Unit ⊕ Unit ⊕ Nat × Nat`) so that statements use only plain definitions; read and
write the five named constructors below (usable as patterns). -/
abbrev TextResult : Type := Nat ⊕ HexError ⊕ Unit ⊕ Unit ⊕ (Nat × Nat)

/-- success: the number -/
@[match_pattern] def TextResult.ok (value : Nat) : TextResult := .inl value

/-- an error of `SetFromHex` -/
@[match_pattern] def TextResult.hexError (e : HexError) : TextResult := .inr (.inl e)

/-- `io.EOF`: the decimal parser found no digits -/
@[match_pattern] def TextResult.decEof : TextResult := .inr (.inr (.inl ()))

/-- `ErrBig256Range` from the decimal parser -/
@[match_pattern] def TextResult.decRange : TextResult := .inr (.inr (.inr (.inl ())))

/-- a `strconv` syntax error from the decimal parser, naming the chunk `s[start, start + len)` -/
@[match_pattern] def TextResult.decSyntax (start len : Nat) : TextResult := .inr (.inr (.inr (.inr (start, len))))

/-- The input starts with the two bytes `'0'` and `'x'` (or `'X'`). -/
def hasHexPrefix : List Nat → Bool
  | 48 :: c :: _ => c == 120 || c == 88
  | _ => false

/-- The outcome of the hex parser, as a `TextResult`. -/
def TextResult.ofHex : HexResult → TextResult
  | .ok v => .ok v
  | .error e => .hexError e

/-- The outcome of the decimal parser, as a `TextResult`. -/
def TextResult.ofDec : DecResult → TextResult
  | .ok v => .ok v
  | .eof => .decEof
  | .range => .decRange
  | .badSyntax start len => .decSyntax start len

/-- THE SPECIFICATION of `UnmarshalText`: hexadecimal when the input has the `0x`/`0X` prefix, decimal otherwise. -/
def unmarshalText (s : List Nat) : TextResult :=
  if hasHexPrefix s then .ofHex (setFromHex s) else .ofDec (setFromDecimal s)

example : unmarshalText [48, 120, 102, 102] = .ok 255 := by decide
example : unmarshalText [50, 53, 53] = .ok 255 := by decide
example : unmarshalText [48, 120] = .hexError .emptyNumber := by decide
example : unmarshalText [] = .decEof := by decide
example : unmarshalText [48, 49] = .ok 1 := by decide

end Fv256.Spec
