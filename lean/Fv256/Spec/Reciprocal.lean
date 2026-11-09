/-!
# `func Reciprocal(m *Int) (mu [5]uint64)`

`Reciprocal(m)` returns a 320-bit approximation `mu` (five 64-bit limbs, least significant first) of `2^512 / m`, used by
`MulModWithReciprocal`. It is only meaningful for `2^192 <= m < 2^256` (top limb non-zero); for smaller `m` it returns zero.
It does not panic. The approximation is NOT exact: the Newton refinement may end a few units below the true quotient
`⌊(2^512 - 1) / m⌋`. The compiled code is proven to return a value in these windows:
* `m < 2^192`: `mu = 0`;
* `2^192 <= m`: `⌊(2^512 - 1) / m⌋ - 3 <= mu <= ⌊(2^512 - 1) / m⌋` (what `MulModWithReciprocal` needs);
* `2^193 <= m`: the tighter `⌊(2^512 - 1) / m⌋ - 1 <= mu <= ⌊(2^512 - 1) / m⌋`.
`mu` is read as the 320-bit number `mu[0] + mu[1] 2^64 + ... + mu[4] 2^256`.
-/

namespace Fv256.Spec

/-- `mu` is an acceptable result of `Reciprocal(m)` (see the file header for the three windows). -/
def IsReciprocal (m mu : Nat) : Prop :=
  (m < 2 ^ 192 → mu = 0) ∧
  (2 ^ 192 ≤ m → (2 ^ 512 - 1) / m - 3 ≤ mu ∧ mu ≤ (2 ^ 512 - 1) / m) ∧
  (2 ^ 193 ≤ m → (2 ^ 512 - 1) / m - 1 ≤ mu ∧ mu ≤ (2 ^ 512 - 1) / m)

/-- Below `2^192` the result is zero. -/
example : IsReciprocal 5 0 := by unfold IsReciprocal; decide

set_option maxRecDepth 100000 in
/-- For `m = 2^255` the exact quotient `⌊(2^512 - 1) / 2^255⌋ = 2^257 - 1` is acceptable. -/
example : IsReciprocal (2 ^ 255) (2 ^ 257 - 1) := by unfold IsReciprocal; decide

end Fv256.Spec
