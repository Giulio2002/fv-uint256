/-!
# `func (z *Int) SetFromHex(hex string) error`

`z.SetFromHex(s)` parses the hexadecimal string `s` into `z`.
* `s` must start with `"0x"` or `"0X"` (`ErrMissingPrefix` otherwise; the empty string is `ErrEmptyString`) and have at least one
  digit after it (`"0x"` alone is `ErrEmptyNumber`).
* A leading zero digit is rejected (`ErrLeadingZero`), except for the single digit `"0x0"`. So `"0x00"` and `"0x01"` fail.
* More than 64 digits fail with `ErrBig256Range`; this is checked before the digits themselves are looked at.
* A byte that is not in `0-9a-fA-F` fails with `ErrSyntax`.
* On success `z` is the number, with `err = nil`. After an error the claim leaves `z` unspecified.

Strings are modelled as lists of byte values (`List Nat`).
-/

namespace Fv256.Spec

/-- The package's sentinel errors that `SetFromHex` can return, as their position in the package's error table (`ErrEmptyString` is `0`,
`ErrMissingPrefix` `1`, `ErrEmptyNumber` `2`, `ErrLeadingZero` `3`, `ErrBig256Range` `4`, `ErrSyntax` `5`); read them by their names below. -/
abbrev HexError : Type := Nat

/-- `ErrEmptyString`: the string is empty -/
def HexError.emptyString : HexError := 0

/-- `ErrMissingPrefix`: the string does not start with `0x` / `0X` -/
def HexError.missingPrefix : HexError := 1

/-- `ErrEmptyNumber`: nothing after the `0x` prefix -/
def HexError.emptyNumber : HexError := 2

/-- `ErrLeadingZero`: the first digit is `0` and more digits follow -/
def HexError.leadingZero : HexError := 3

/-- `ErrBig256Range`: more than 64 digits -/
def HexError.big256Range : HexError := 4

/-- `ErrSyntax`: a digit position holds a byte that is not hexadecimal -/
def HexError.badSyntax : HexError := 5

/-- The outcome of `SetFromHex` (and of `FromHex`, `MustFromHex`): the parsed number (`.ok v`) or one of the errors (`.error e`). -/
abbrev HexResult : Type := Except HexError Nat

/-- The position of the error in the package's error table (the error already is that number). Used only to look an error up in the table. -/
def HexError.tag (e : HexError) : Nat := e

/-- Value of a hexadecimal digit byte: `0-9` are `0..9`, `a-f` and `A-F` are `10..15`; `none` for every other byte. -/
def hexDigitValue (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- THE SPECIFICATION of `SetFromHex`: the result for the string whose bytes are `s`. Checks run in the order of the Go source:
empty, prefix, empty number, leading zero, more than 64 digits, then the digits. -/
def setFromHex (s : List Nat) : HexResult :=
  match s with
  | [] => .error .emptyString
  | [_] => .error .missingPrefix
  | c0 :: c1 :: digits =>
    if c0 ≠ 48 ∨ (c1 ≠ 120 ∧ c1 ≠ 88) then .error .missingPrefix
    else if digits = [] then .error .emptyNumber
    else if 1 < digits.length ∧ digits.head? = some 48 then .error .leadingZero
    else if 64 < digits.length then .error .big256Range
    else if digits.all (fun c => (hexDigitValue c).isSome) then
      .ok (digits.foldl (fun acc c => acc * 16 + (hexDigitValue c).getD 0) 0)
    else .error .badSyntax

-- cheap sanity checks ("0xff" is [48, 120, 102, 102])
example : setFromHex [48, 120, 102, 102] = .ok 255 := by rfl
example : setFromHex [48, 88, 70] = .ok 15 := by rfl
example : setFromHex [48, 120, 48] = .ok 0 := by rfl
example : setFromHex [] = .error .emptyString := by rfl
example : setFromHex [48] = .error .missingPrefix := by rfl
example : setFromHex [49, 120, 49] = .error .missingPrefix := by rfl
example : setFromHex [48, 120] = .error .emptyNumber := by rfl
example : setFromHex [48, 120, 48, 49] = .error .leadingZero := by rfl
example : setFromHex [48, 120, 103] = .error .badSyntax := by rfl
example : setFromHex ([48, 120] ++ List.replicate 65 49) = .error .big256Range := by rfl
example : setFromHex ([48, 120] ++ List.replicate 64 102) = .ok (2 ^ 256 - 1) := by rfl

end Fv256.Spec
