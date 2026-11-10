import Fv256.Spec.I
import Fv256.Spec.SetFromDecimal

/-!
# `func (dst *Int) Scan(src interface{}) error`

`dst.Scan(src)` implements `database/sql.Scanner` and decodes a database value:
* `src == nil` sets `dst = 0` and returns `nil`;
* a `string` or `[]byte` is read as a decimal number with an optional exponent (`"12e3"` is `12000`): the empty string is `0`; a string
  without `'e'` is parsed like `SetFromDecimal`; otherwise the part before the first `'e'` is the mantissa (parsed like `SetFromDecimal`)
  and the part after it is the exponent (also parsed like `SetFromDecimal`; the exponent `"0"` is accepted without further checks). The result
  is `mantissa * 10^exponent`, or `ErrBig256Range` if the exponent exceeds 77 or the product does not fit in 256 bits;
* any other type fails with the error `errors.New("unsupported type")`.
Errors of the number parsers (`io.EOF`, `ErrBig256Range`, `strconv` syntax errors) are returned unchanged; a syntax error names the 19-digit
chunk of the exponent counted in the ORIGINAL string.
-/

namespace Fv256.Spec

/-- The dynamic value passed to `Scan`: `nil`, a string / byte slice (its bytes), or a value of another type. A sum of core types
(`Unit ⊕ List Nat ⊕ Unit`); read and write the three named constructors below (usable as patterns). -/
abbrev ScanSource : Type := Unit ⊕ List Nat ⊕ Unit

/-- `src == nil` -/
@[match_pattern] def ScanSource.nil : ScanSource := .inl ()

/-- a `string` or a `[]byte` with these bytes -/
@[match_pattern] def ScanSource.text (bytes : List Nat) : ScanSource := .inr (.inl bytes)

/-- a value of any other type -/
@[match_pattern] def ScanSource.other : ScanSource := .inr (.inr ())

/-- The outcome of `Scan`: the number, one of the decimal-parser errors, or the "unsupported type" error. A sum of core types
(`Nat ⊕ Unit ⊕ Unit ⊕ Nat × Nat ⊕ Unit`); read and write the five named constructors below (usable as patterns). -/
abbrev ScanResult : Type := Nat ⊕ Unit ⊕ Unit ⊕ (Nat × Nat) ⊕ Unit

/-- success: `dst` becomes this number and `err = nil` -/
@[match_pattern] def ScanResult.ok (value : Nat) : ScanResult := .inl value

/-- `io.EOF` (no digits in the mantissa or exponent) -/
@[match_pattern] def ScanResult.eof : ScanResult := .inr (.inl ())

/-- `ErrBig256Range` -/
@[match_pattern] def ScanResult.range : ScanResult := .inr (.inr (.inl ()))

/-- a `strconv` syntax error naming the chunk `s[start, start + len)` of the original string -/
@[match_pattern] def ScanResult.badSyntax (start len : Nat) : ScanResult := .inr (.inr (.inr (.inl (start, len))))

/-- `errors.New("unsupported type")` -/
@[match_pattern] def ScanResult.unsupported : ScanResult := .inr (.inr (.inr (.inr ())))

/-- The number denoted by the bytes of a `string` / `[]byte` given to `Scan`: decimal with an optional `e` exponent, as described above. -/
def scanText (s : List Nat) : DecResult :=
  if s = [] then .ok 0
  else match s.findIdx? (· == 101) with
    | none => setFromDecimal s
    | some i =>
      match setFromDecimal (s.take i) with
      | .ok v =>
        if s.drop (i + 1) = [48] then .ok v
        else match setFromDecimal (s.drop (i + 1)) with
          | .ok e => if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then .range else .ok (v * 10 ^ e)
          | .badSyntax start len => .badSyntax (i + 1 + start) len
          | r => r
      | r => r

/-- THE SPECIFICATION of `Scan`: `nil` is `0`, text is `scanText`, anything else is the "unsupported type" error. -/
def scan : ScanSource → ScanResult
  | .nil => .ok 0
  | .text s => match scanText s with
    | .ok v => .ok v
    | .eof => .eof
    | .range => .range
    | .badSyntax start len => .badSyntax start len
  | .other => .unsupported

-- cheap sanity checks ("12e3" is [49, 50, 101, 51])
example : scanText [49, 50, 101, 51] = .ok 12000 := by decide
example : scanText [] = .ok 0 := by decide
example : scanText [49, 50] = .ok 12 := by decide
example : scanText [49, 101, 48] = .ok 1 := by decide
example : scanText [101, 49] = .eof := by decide
example : scanText [49, 101, 55, 56] = .range := by decide
example : scan .nil = .ok 0 := by decide
example : scan .other = .unsupported := by decide

end Fv256.Spec

/-! ### Implementation-shaped form used by the machine-level statements (bytes as a function, `Res` triples)

`Fv256/Proofs/Common/ScanBridge.lean` proves it agrees with `Fv256.Spec.scanText`. -/

open Fv256.I

namespace Fv256.ScanSpec

/-- the index of the first `'e'` among the first `n` bytes -/
def idxE (b : Nat → Nat) (n : Nat) : Option Nat := (List.range n).find? (fun i => b i == 101)

/-- the outcome of `scanScientificFromString` on the bytes `b 0 .. b (n-1)` -/
noncomputable def sciParse (b : Nat → Nat) (n : Nat) : Res :=
  if n = 0 then Res.ok 0 else
  match idxE b n with
  | none => decParse b n
  | some i =>
    match decParse b i with
    | Res.ok v =>
      if n - (i + 1) = 1 ∧ b (i + 1) = 48 then Res.ok v else
      match decParse (fun k => b (i + 1 + k)) (n - (i + 1)) with
      | Res.ok e => if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e)
      | Res.syntax lo len => Res.syntax (i + 1 + lo) len
      | r => r
    | r => r

end Fv256.ScanSpec
