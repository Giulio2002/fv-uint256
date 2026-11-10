/-!
# `func (z *Int) Hex() string`

`z.Hex()` returns `"0x"` followed by the lowercase hexadecimal digits of `z`, most significant first, with no leading zeros
(`0` is `"0x0"`). It never fails and never panics. Strings are modelled as lists of ASCII byte values.
-/

namespace Fv256.Spec

/-- The ASCII bytes returned by `z.Hex()`: `'0'`, `'x'`, then the lowercase base-16 digits of `x` (`0-9a-f`) without leading zeros. -/
def hex (x : Nat) : List Nat := 48 :: 120 :: (Nat.toDigits 16 x).map Char.toNat

example : hex 0 = [48, 120, 48] := by decide
example : hex 255 = [48, 120, 102, 102] := by decide
example : hex 4096 = [48, 120, 49, 48, 48, 48] := by decide

end Fv256.Spec
