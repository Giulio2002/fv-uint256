import Fv256.Spec.Dec
import Fv256.Spec.Hex

/-!
# `func (z *Int) Format(s fmt.State, ch rune)`

`*uint256.Int` implements `fmt.Formatter`, so `fmt.Fprintf(w, "%d", z)` calls `z.Format(s, 'd')`, where `s` is the formatting state
(an interface the caller supplies: it answers `Width()`, `Precision()` and `Flag(c)` queries and receives the output through `Write`).
What `Format` does:

* **nil receiver** (`z == nil`): `fmt.Fprint(s, "<nil>")`, i.e. the five bytes `<nil>`, whatever the verb and flags.
* **plain request** (`z != nil`, no width, no precision, none of the flags `+`, ` `, `-`, `0`, `#`, and the verb is `d`, `v`, `s` or `x`):
  exactly one call `s.Write(bytes)`, where `bytes` are the decimal digits of `*z` (verbs `d`, `v`, `s`) or its lowercase hexadecimal digits
  without any `0x` prefix (verb `x`). No padding, no sign, no newline.
* **anything else** (any width, precision or flag, or another verb such as `X`, `b`, `o`, `O`, `q`): the request is delegated to
  `math/big`: `z.ToBig().Format(s, ch)`; its output is whatever `math/big` writes and is not modelled here.

`Format` never panics on its own. Strings are modelled as lists of ASCII byte values; the receiver is `none` for a nil pointer and
`some x` for a pointer to the number `x`.
-/

namespace Fv256.Spec

/-- The `fmt.State` answers `Format` looks at: whether a width and a precision are set, and the five flags it checks. -/
structure FormatRequest where
  /-- `s.Width()` reports a width -/
  hasWidth : Bool
  /-- `s.Precision()` reports a precision -/
  hasPrecision : Bool
  /-- `s.Flag('+')` -/
  plus : Bool
  /-- `s.Flag(' ')` -/
  space : Bool
  /-- `s.Flag('-')` -/
  minus : Bool
  /-- `s.Flag('0')` -/
  zero : Bool
  /-- `s.Flag('#')` -/
  sharp : Bool

/-- A request with no width, no precision and no flag: the only kind `Format` answers without `math/big`. -/
@[reducible] def FormatRequest.plain (q : FormatRequest) : Prop :=
  q.hasWidth = false ∧ q.hasPrecision = false ∧ q.plus = false ∧ q.space = false ∧ q.minus = false ∧ q.zero = false ∧ q.sharp = false

/-- The verbs `Format` handles itself: `d`, `s`, `v` (decimal) and `x` (lowercase hexadecimal), as ASCII codes. -/
@[reducible] def fastVerb (verb : Nat) : Prop := verb = 100 ∨ verb = 115 ∨ verb = 118 ∨ verb = 120

/-- The digit bytes of the single `Write` of a plain request: lowercase hexadecimal without prefix for the verb `x` (120), otherwise decimal. -/
def fastBytes (verb x : Nat) : List Nat := if verb = 120 then (hex x).drop 2 else dec x

/-- The bytes `fmt.Fprint(s, "<nil>")` writes for a nil receiver. -/
def nilText : List Nat := [60, 110, 105, 108, 62]

/-- What one call of `Format` does to its `fmt.State`. -/
inductive FormatEffect where
  /-- exactly one call `s.Write(bytes)` and nothing else -/
  | write (bytes : List Nat)
  /-- `fmt.Fprint(s, "<nil>")`, which writes `bytes` -/
  | fprintNil (bytes : List Nat)
  /-- `z.ToBig().Format(s, ch)`: the output is `math/big`'s -/
  | viaBig
  deriving DecidableEq

/-- THE SPECIFICATION of `z.Format(s, verb)` for the receiver `x` (`none` = nil pointer) and the state's answers `q`: a nil receiver
prints `<nil>`; a plain request with verb `d`/`s`/`v`/`x` writes the digits of `x`; everything else is delegated to `math/big`. -/
def format (verb : Nat) (q : FormatRequest) (x : Option Nat) : FormatEffect :=
  match x with
  | none => .fprintNil nilText
  | some n => if q.plain ∧ fastVerb verb then .write (fastBytes verb n) else .viaBig

/-- The request with every answer "no". -/
def FormatRequest.none : FormatRequest := ⟨false, false, false, false, false, false, false⟩

example : format 100 .none (some 255) = .write [50, 53, 53] := by decide
example : format 118 .none (some 255) = .write [50, 53, 53] := by decide
example : format 120 .none (some 255) = .write [102, 102] := by decide
example : format 120 .none (some 0) = .write [48] := by decide
example : format 100 .none none = .fprintNil [60, 110, 105, 108, 62] := by decide
example : format 88 .none (some 255) = .viaBig := by decide
example : format 100 { FormatRequest.none with sharp := true } (some 255) = .viaBig := by decide
example : format 100 { FormatRequest.none with hasWidth := true } (some 255) = .viaBig := by decide

end Fv256.Spec
