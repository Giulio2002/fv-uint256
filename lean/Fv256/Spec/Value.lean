/-!
# `func (src *Int) Value() (driver.Value, error)`

`z.Value()` is the `database/sql/driver.Valuer` implementation: it returns the number as its BASE-10 STRING (the result of `Dec()`),
boxed in an interface value (`driver.Value` is `any`, here holding a `string`), and a nil error. Like `Dec()`, the string has no
leading zeros and no sign (`0` is `"0"`). It cannot fail.
-/

namespace Fv256.Spec

/-- The bytes of the string `z.Value()` returns for the number `x` held in `z`: the ASCII codes of the decimal digits of `x`, most
significant first, with no leading zeros (`0` gives `"0"`). -/
def value (x : Nat) : List Nat :=
  if x < 10 then [48 + x] else value (x / 10) ++ [48 + x % 10]
termination_by x
decreasing_by omega

/-- Zero is the one-character string `"0"`. -/
example : value 0 = [48] := by simp [value]

/-- No leading zeros. -/
example : value 123 = [49, 50, 51] := by simp [value]

/-- The largest 64-bit-boundary neighbour: `100` has three digits. -/
example : value 100 = [49, 48, 48] := by simp [value]

end Fv256.Spec
