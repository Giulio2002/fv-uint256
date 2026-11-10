import Fv256.Spec.Dec

/-!
# `func (z *Int) PrettyDec(sep byte) string`

`z.PrettyDec(sep)` returns the decimal representation of `z` with the separator byte `sep` inserted between every group of three
digits counted from the right (`1234567` with `','` is `"1,234,567"`; numbers below `1000` get no separator). It never fails and
never panics.
-/

namespace Fv256.Spec

/-- The three decimal digits of `n % 1000`, zero padded (`7` is `"007"`). -/
def pad3 (n : Nat) : List Nat := [48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10]

/-- The ASCII bytes returned by `z.PrettyDec(sep)`: below `1000` the plain digits; otherwise the grouped digits of `x / 1000`,
then `sep`, then the three zero-padded digits of `x % 1000`. -/
def prettyDec (sep : Nat) (x : Nat) : List Nat :=
  if x < 1000 then dec x else prettyDec sep (x / 1000) ++ sep :: pad3 (x % 1000)
termination_by x
decreasing_by omega

-- (`prettyDec` is defined by well-founded recursion, so `decide` cannot unfold it; `simp` can)
example : prettyDec 44 1234567 = [49, 44, 50, 51, 52, 44, 53, 54, 55] := by
  simp [prettyDec, dec, pad3]; decide
example : prettyDec 44 999 = [57, 57, 57] := by simp [prettyDec, dec]; decide
example : prettyDec 44 0 = [48] := by simp [prettyDec, dec]

end Fv256.Spec
