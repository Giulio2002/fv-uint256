import Fv256.Spec

/-!
# Independent specification, family C (conversion, parsing, encoding)

Plain mathematical models, written without reference to the Go code.
-/

namespace Fv256.C

open Fv256.Spec

/-- The natural number whose `n` little-endian 64-bit words are `w 0, w 1, ..., w (n-1)`
(word `i` has weight `2^(64 i)`): the magnitude of a `big.Int` with `n` words. -/
def bigAbs (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bigAbs w n + w n * 2 ^ (64 * n)

/-- `z.SetFromBig(b)`: the value stored in `z` for a `big.Int` of sign `neg` and magnitude `abs`:
the magnitude reduced modulo `2^256`, negated modulo `2^256` when `neg`. -/
def fromBig (neg : Bool) (abs : Nat) : Nat := if neg then Spec.neg (abs % W) else abs % W

/-- `z.SetFromBig(b)` overflow flag: the magnitude has more than `256/64 = 4` words. -/
def fromBigOv (len : Nat) : Bool := decide (4 < len)

/-- The integer value of a `big.Int` with sign flag `neg` and magnitude `abs`. -/
def bigVal (neg : Bool) (abs : Nat) : Int := if neg then -(abs : Int) else (abs : Int)

/-- `z.CmpBig(x)`: -1, 0 or +1 as the number `z` is smaller than, equal to, or larger than the integer `b`. -/
def cmpBig (z : Nat) (b : Int) : Int := if (z : Int) < b then -1 else if (z : Int) = b then 0 else 1

/-! ## Hexadecimal parsing (`SetFromHex`, `FromHex`, `MustFromHex`) -/

/-- the value of an ASCII hexadecimal digit (`0-9`, `a-f`, `A-F`); `none` for every other byte. -/
def hexNib (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- the digit value at position `k` of the byte sequence `b` (`0` for a non-digit). -/
def hexDigit (b : Nat → Nat) (k : Nat) : Nat := (hexNib (b k)).getD 0

/-- the positional value (base 16, most significant digit first) of the `n` digits `b a, ..., b (a+n-1)`. -/
def hexSum (b : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => hexSum b a n * 16 + hexDigit b (a + n)

/-- every byte of `[a, c)` is a hexadecimal digit. -/
def allHex (b : Nat → Nat) (a c : Nat) : Prop := ∀ k, a ≤ k → k < c → (hexNib (b k)).isSome

open Classical in
/-- `SetFromHex(s)` for the string whose bytes are `b 0, ..., b (n-1)`: the number, or the error.
`"0x"` or `"0X"` prefix required, at least one digit, no leading zero digit (except the single digit `"0x0"`),
at most 64 digits, only hexadecimal digits. The errors are the package's sentinel errors, tagged by a number:
`0` `ErrEmptyString`, `1` `ErrMissingPrefix`, `2` `ErrEmptyNumber`, `3` `ErrLeadingZero`, `4` `ErrBig256Range`,
`5` `ErrSyntax`. -/
noncomputable def parseHex (b : Nat → Nat) (n : Nat) : Except Nat Nat :=
  if n = 0 then .error 0
  else if n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88) then .error 1
  else if n = 2 then .error 2
  else if 3 < n ∧ b 2 = 48 then .error 3
  else if 66 < n then .error 4
  else if allHex b 2 n then .ok (hexSum b 2 (n - 2)) else .error 5

end Fv256.C
