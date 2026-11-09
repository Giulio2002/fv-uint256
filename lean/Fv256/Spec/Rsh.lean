/-!
# `func (z *Int) Rsh(x *Int, n uint) *Int`

`z.Rsh(x, n)` sets `z = x >> n` (logical shift: zeros enter at the top, the low `n` bits are dropped, i.e. `x / 2^n` rounded
down) and returns `z`. A shift by `256` or more (`n` is any `uint`) gives `0`. There is no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Rsh(x, n)`: `x / 2^n` rounded down (`0` once `n ≥ 256`, since `x < 2^256`). -/
def rsh (x n : Nat) : Nat := x / 2 ^ n

/-- Shifting by one halves, rounding down. -/
example : rsh 7 1 = 3 := by decide

/-- A shift by the full word width clears everything. -/
example : rsh (2 ^ 256 - 1) 256 = 0 := by decide

end Fv256.Spec
