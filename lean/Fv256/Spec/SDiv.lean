import Fv256.Spec.Div

/-!
# `func (z *Int) SDiv(n, d *Int) *Int`

`z.SDiv(n, d)` reads `n` and `d` as two's complement signed 256-bit integers (a word `>= 2^255` is negative), divides with
truncation toward zero, stores the result as a two's complement word in `z` and returns `z`.
The magnitude of the result is `|n| / |d|` (rounded down); it is negative exactly when the signs of `n` and `d` differ.
Division by zero is NOT an error and does not panic: the result is `0`.
The one overflowing case `-2^255 / -1` wraps to `-2^255` (the word `2^255`), as in the EVM.
-/

namespace Fv256.Spec

/-- Two's complement negation of a word: `2^256 - x`, wrapped (so `negate 0 = 0`). -/
def negate (x : Nat) : Nat := (2 ^ 256 - x) % 2 ^ 256

/-- Absolute value of a two's complement word, as a word: `x` if `x < 2^255` (non-negative), else `negate x`
(for `x = 2^255` this is `2^255` again, the unsigned magnitude of `-2^255`). -/
def magnitude (x : Nat) : Nat := if x < 2 ^ 255 then x else (2 ^ 256 - x) % 2 ^ 256

/-- Value of `z.SDiv(n, d)`: the unsigned quotient of the magnitudes, negated when exactly one operand is negative;
`0` when `d = 0`. -/
def sdiv (n d : Nat) : Nat :=
  if (2 ^ 255 ≤ n ↔ 2 ^ 255 ≤ d) then div (magnitude n) (magnitude d)
  else negate (div (magnitude n) (magnitude d))

/-- `-7 / 2 = -3` (truncation toward zero): `-7` is the word `2^256 - 7` and `-3` is `2^256 - 3`. -/
example : sdiv (2 ^ 256 - 7) 2 = 2 ^ 256 - 3 := by decide

/-- `-7 / -2 = 3`. -/
example : sdiv (2 ^ 256 - 7) (2 ^ 256 - 2) = 3 := by decide

/-- `7 / -2 = -3`. -/
example : sdiv 7 (2 ^ 256 - 2) = 2 ^ 256 - 3 := by decide

/-- Division by zero gives zero. -/
example : sdiv (2 ^ 256 - 7) 0 = 0 := by decide

/-- The overflow case: `-2^255 / -1 = -2^255` (wraps). -/
example : sdiv (2 ^ 255) (2 ^ 256 - 1) = 2 ^ 255 := by decide

end Fv256.Spec
