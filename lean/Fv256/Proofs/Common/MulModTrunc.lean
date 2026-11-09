import Fv256.Proofs.Common.MulModMath

/-!
# The truncated quotient product of `reduce4` (pure `Nat`)

`q1 = x / 2^192` has limbs `a0..a4` (= `x[3..7]`), `mu` has limbs `u0..u4`.  `reduce4` adds, limb by limb, all partial products of
index `i + j ≥ 4` in full and only the high word of those of index `3`; everything else is dropped.  `T` is that sum (as a number):
`T ≤ q1 * mu < T + 2^320`, so the code's quotient `⌊T / 2^320⌋` is the true Barrett quotient or one less.
-/

namespace Fv256.F

theorem trunc_q (P T a0 a1 a2 a3 a4 u0 u1 u2 u3 u4 : Nat)
    (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64) (h4 : a4 < 2 ^ 64)
    (g0 : u0 < 2 ^ 64) (g1 : u1 < 2 ^ 64) (g2 : u2 < 2 ^ 64) (g3 : u3 < 2 ^ 64) (g4 : u4 < 2 ^ 64)
    (hP : P = (a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4) * (u0 + 2 ^ 64 * u1 + 2 ^ 128 * u2 + 2 ^ 192 * u3 + 2 ^ 256 * u4))
    (hT : T = 2 ^ 256 * ((a3 * u0 / 2 ^ 64) + (a2 * u1 / 2 ^ 64) + (a1 * u2 / 2 ^ 64) + (a0 * u3 / 2 ^ 64)) +
      2 ^ 256 * (a4 * u0 + a3 * u1 + a2 * u2 + a1 * u3 + a0 * u4) +
      2 ^ 320 * (a4 * u1 + a3 * u2 + a2 * u3 + a1 * u4) +
      2 ^ 384 * (a4 * u2 + a3 * u3 + a2 * u4) +
      2 ^ 448 * (a4 * u3 + a3 * u4) +
      2 ^ 512 * (a4 * u4)) :
    T ≤ P ∧ P < T + 2 ^ 320 := by
  have e : P = a0 * u0 + 2 ^ 64 * (a0 * u1 + a1 * u0) + 2 ^ 128 * (a0 * u2 + a1 * u1 + a2 * u0) +
      2 ^ 192 * (a0 * u3 + a1 * u2 + a2 * u1 + a3 * u0) + 2 ^ 256 * (a0 * u4 + a1 * u3 + a2 * u2 + a3 * u1 + a4 * u0) +
      2 ^ 320 * (a1 * u4 + a2 * u3 + a3 * u2 + a4 * u1) + 2 ^ 384 * (a2 * u4 + a3 * u3 + a4 * u2) +
      2 ^ 448 * (a3 * u4 + a4 * u3) + 2 ^ 512 * (a4 * u4) := by
    rw [hP]; janus_ring
  have bd : ∀ a u : Nat, a < 2 ^ 64 → u < 2 ^ 64 → a * u < 2 ^ 128 := by
    intro a u ha hu
    have := Nat.mul_lt_mul'' ha hu
    rwa [← Nat.pow_add] at this
  have b00 := bd a0 u0 h0 g0
  have b01 := bd a0 u1 h0 g1
  have b10 := bd a1 u0 h1 g0
  have b02 := bd a0 u2 h0 g2
  have b11 := bd a1 u1 h1 g1
  have b20 := bd a2 u0 h2 g0
  have d30 := Nat.div_add_mod (a3 * u0) (2 ^ 64)
  have d21 := Nat.div_add_mod (a2 * u1) (2 ^ 64)
  have d12 := Nat.div_add_mod (a1 * u2) (2 ^ 64)
  have d03 := Nat.div_add_mod (a0 * u3) (2 ^ 64)
  have m30 := Nat.mod_lt (a3 * u0) (Nat.two_pow_pos 64)
  have m21 := Nat.mod_lt (a2 * u1) (Nat.two_pow_pos 64)
  have m12 := Nat.mod_lt (a1 * u2) (Nat.two_pow_pos 64)
  have m03 := Nat.mod_lt (a0 * u3) (Nat.two_pow_pos 64)
  rw [e, hT]
  constructor <;> omega

end Fv256.F
