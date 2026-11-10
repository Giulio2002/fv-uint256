/-!
# `func (z *Int) Lsh(x *Int, n uint) *Int`

`z.Lsh(x, n)` sets `z = x << n` and returns `z`: the bits of `x` move up by `n` places and the bits that leave the top of the
256-bit word are dropped (arithmetic modulo `2^256`). A shift by `256` or more (`n` is any `uint`) gives `0`.
There is no error or panic case.
-/

namespace Fv256.Spec

/-- Value of `z.Lsh(x, n)`: `x * 2^n` wrapped modulo `2^256` (so `0` once `n ≥ 256`, since then `2^256` divides `2^n`). -/
def lsh (x n : Nat) : Nat := x * 2 ^ n % 2 ^ 256

/-- Shifting by one doubles. -/
example : lsh 3 1 = 6 := by decide

/-- The top bit falls off the word. -/
example : lsh (2 ^ 255) 1 = 0 := by decide

/-- A shift by the full word width clears everything. -/
example : lsh 5 256 = 0 := by decide

end Fv256.Spec
