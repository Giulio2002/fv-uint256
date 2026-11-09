/-!
# `func (z *Int) SetFromDecimal(s string) (err error)`

`z.SetFromDecimal(s)` parses the ASCII decimal string `s` into `z`.
* An optional single leading `+` is accepted, and any number of leading zeros are ignored (`"+007"` is `7`, `"000"` is `0`).
* The digits must then be a decimal number `<= 2^256 - 1`; a longer or larger one fails with `ErrBig256Range`.
* Nothing left after the sign (`""`, `"+"`) fails with `io.EOF`.
* A non-digit byte fails with a `strconv` syntax error that names the 19-digit chunk (counted from the least significant end)
  holding the first offending byte.
* On success `z` is the parsed number, on `io.EOF` `z` is `0`, on `ErrBig256Range` `z` is unchanged; after a syntax error the
  claim says only that nothing outside `z` and the allocated error object changes.

Strings are modelled as lists of byte values (`List Nat`).
-/

namespace Fv256.Spec

/-- The outcome of `SetFromDecimal`: the parsed number, or one of the three documented errors. -/
inductive DecResult where
  /-- success: `z` becomes this number (and `err = nil`) -/
  | ok (value : Nat)
  /-- `err = io.EOF`: no digits at all after the optional `+` -/
  | eof
  /-- `err = ErrBig256Range`: the number does not fit in 256 bits -/
  | range
  /-- `err = *strconv.NumError{Err: ErrSyntax}` whose `Num` is the chunk `s[start, start + len)` of the original string -/
  | badSyntax (start len : Nat)
  deriving DecidableEq, Repr

/-- ASCII decimal digit `'0'..'9'`. -/
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- Remove at most one leading `'+'` (byte 43). -/
def dropPlus : List Nat → List Nat
  | 43 :: t => t
  | s => s

/-- Remove leading `'0'` bytes (48), but keep one `'0'` if that would empty a non-empty string, so `"000"` is `0` and not EOF. -/
def dropZeros (s : List Nat) : List Nat :=
  match s.dropWhile (· == 48), s with
  | [], _ :: _ => [48]
  | t, _ => t

/-- The digit string to parse: `s` without its optional `+` and without leading zeros. -/
def body (s : List Nat) : List Nat := dropZeros (dropPlus s)

/-- The decimal digits of `2^256 - 1` as ASCII codes (78 of them): the largest accepted number. -/
def maxDigits : List Nat := (toString (2 ^ 256 - 1)).toList.map Char.toNat

/-- Numeric value of a digit string, most significant digit first. -/
def digitsValue (t : List Nat) : Nat := t.foldl (fun a c => a * 10 + (c - 48)) 0

/-- The first chunk (scanning 19-byte chunks from the least significant end, at most 5 of them) that holds a non-digit, as
`(start, len)` positions in the original string `s`; `p` is where the body starts. -/
def firstBadChunk (s : List Nat) (p : Nat) : Option (Nat × Nat) :=
  (List.range 5).findSome? fun i =>
    if s.length - p ≤ 19 * i then none
    else
      let hi := s.length - 19 * i
      let lo := if p + 19 ≤ hi then hi - 19 else p
      if ((s.drop lo).take (hi - lo)).all isDigit then none else some (lo, hi - lo)

/-- Parse the body (at most 78 digits, already known not to be too large when 78 long). -/
def parseBody (s : List Nat) : DecResult :=
  let p := s.length - (body s).length
  if (body s) = [] then .eof
  else match firstBadChunk s p with
    | some (lo, len) => .badSyntax lo len
    | none => .ok (digitsValue (body s))

/-- THE SPECIFICATION of `SetFromDecimal`: the result for the string whose bytes are `s`. More than 78 digits, or exactly 78
digits lexicographically above `2^256 - 1`, is `ErrBig256Range` (checked before any syntax error, as in the Go source). -/
def setFromDecimal (s : List Nat) : DecResult :=
  if (body s).length < 78 then parseBody s
  else if (body s).length = 78 then (if maxDigits < body s then .range else parseBody s)
  else .range

-- cheap sanity checks ("123" is [49, 50, 51])
example : setFromDecimal [49, 50, 51] = .ok 123 := by decide
example : setFromDecimal [43, 48, 48, 55] = .ok 7 := by decide
example : setFromDecimal [48, 48, 48] = .ok 0 := by decide
example : setFromDecimal [] = .eof := by decide
example : setFromDecimal [43] = .eof := by decide
example : setFromDecimal [49, 120] = .badSyntax 0 2 := by decide

end Fv256.Spec
