import Fv256.Proofs.Common.MulModTrunc

/-! `reduce4` (arm64): pure-Nat glue between the machine quotient estimate and `MulModMath.reduce_value`. -/

namespace Fv256.Arm64.R4Nat
open Fv256.F

/-- the machine quotient `q = ⌊T / 2^320⌋` (`T` the truncated product sum) satisfies the hypotheses of `reduce_value` -/
theorem q_ok (x mu T a0 a1 a2 a3 a4 u0 u1 u2 u3 u4 : Nat)
    (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64) (h4 : a4 < 2 ^ 64)
    (g0 : u0 < 2 ^ 64) (g1 : u1 < 2 ^ 64) (g2 : u2 < 2 ^ 64) (g3 : u3 < 2 ^ 64) (g4 : u4 < 2 ^ 64)
    (ha : x / 2 ^ 192 = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3 + 2 ^ 256 * a4)
    (hu : mu = u0 + 2 ^ 64 * u1 + 2 ^ 128 * u2 + 2 ^ 192 * u3 + 2 ^ 256 * u4)
    (hT : T = 2 ^ 256 * ((a3 * u0 / 2 ^ 64) + (a2 * u1 / 2 ^ 64) + (a1 * u2 / 2 ^ 64) + (a0 * u3 / 2 ^ 64)) +
      2 ^ 256 * (a4 * u0 + a3 * u1 + a2 * u2 + a1 * u3 + a0 * u4) +
      2 ^ 320 * (a4 * u1 + a3 * u2 + a2 * u3 + a1 * u4) +
      2 ^ 384 * (a4 * u2 + a3 * u3 + a2 * u4) +
      2 ^ 448 * (a4 * u3 + a3 * u4) +
      2 ^ 512 * (a4 * u4)) :
    x / 2 ^ 192 * mu / 2 ^ 320 ≤ T / 2 ^ 320 + 1 ∧ T / 2 ^ 320 ≤ x / 2 ^ 192 * mu / 2 ^ 320 := by
  have hq := trunc_q (x / 2 ^ 192 * mu) T a0 a1 a2 a3 a4 u0 u1 u2 u3 u4 h0 h1 h2 h3 h4 g0 g1 g2 g3 g4
    (by rw [ha, hu]) hT
  have he := trunc_est (x / 2 ^ 192 * mu) T (2 ^ 320) (Nat.two_pow_pos 320) hq.1 hq.2
  exact ⟨he.2, he.1⟩

end Fv256.Arm64.R4Nat
