import Fv256.Spec.MulMod

/-!
# `func (z *Int) MulModWithReciprocal(x, y, m *Int, mu *[5]uint64) *Int`

`z.MulModWithReciprocal(x, y, m, mu)` computes the same value as `MulMod`: `z = (x * y) mod m` (exact product, `0` for `m = 0`),
but is given the precomputed 320-bit reciprocal `mu` of `m` to speed up the reduction. The caller promises that `mu` really is the
reciprocal of `m` (see `muOk`); the result never depends on `mu` otherwise. No call panics.
-/

namespace Fv256.Spec

/-- The caller's promise about the reciprocal `mu` of the modulus `m` (the number held in the 5 words of `mu`): when `m` has four
non-zero-led words (`2^192 <= m`), `mu` lies in the window `⌊(2^512 - 1) / m⌋ - 3 <= mu <= ⌊(2^512 - 1) / m⌋` (a true
`Reciprocal(m)` is at most one below the upper end; the proof only needs this weaker window). For smaller `m` the argument is unused. -/
def muOk (m mu : Nat) : Prop :=
  2 ^ 192 ≤ m → (2 ^ 512 - 1) / m - 3 ≤ mu ∧ mu ≤ (2 ^ 512 - 1) / m

/-- Value of `z.MulModWithReciprocal(x, y, m, mu)` (when `muOk m mu`): the same as `MulMod`; the reciprocal only changes how fast. -/
def mulModWithReciprocal (x y m : Nat) : Nat := mulMod x y m

/-- The result is the plain modular product. -/
example : mulModWithReciprocal 5 4 7 = 6 := by decide

/-- A zero modulus gives zero (and needs no reciprocal: `muOk 0 mu` holds for every `mu`). -/
example : mulModWithReciprocal 5 4 0 = 0 := by decide

end Fv256.Spec
