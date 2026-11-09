import Fv256.Proofs.Arm64.R4Nat
import Fv256.Proofs.Arm64.R4Ro

/-! `reduce4` (arm64): pure-Nat glue (the machine quotient and remainder equal the Barrett quantities of `MulModMath`). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 1024
namespace Fv256.Arm64.R4Nat
open Fv256.F

theorem r4_glue (xl0 xl1 xl2 xl3 xl4 xl5 xl6 xl7 ml0 ml1 ml2 ml3 ul0 ul1 ul2 ul3 ul4 V Bl C r8 D T : Nat)
    (bx0 : xl0 < 2 ^ 64) (bx1 : xl1 < 2 ^ 64) (bx2 : xl2 < 2 ^ 64) (bx3 : xl3 < 2 ^ 64) (bx4 : xl4 < 2 ^ 64) (bx5 : xl5 < 2 ^ 64)
    (bx6 : xl6 < 2 ^ 64) (bx7 : xl7 < 2 ^ 64)
    (bm0 : ml0 < 2 ^ 64) (bm1 : ml1 < 2 ^ 64) (bm2 : ml2 < 2 ^ 64) (bm3 : ml3 < 2 ^ 64)
    (bu0 : ul0 < 2 ^ 64) (bu1 : ul1 < 2 ^ 64) (bu2 : ul2 < 2 ^ 64) (bu3 : ul3 < 2 ^ 64) (bu4 : ul4 < 2 ^ 64)
    (hm3 : ml3 ≠ 0)
    (hmuw : RecipWeak (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3) (ul0 + 2 ^ 64 * ul1 + 2 ^ 128 * ul2 + 2 ^ 192 * ul3 + 2 ^ 256 * ul4))
    (hT : T = 2 ^ 256 * ((xl6 * ul0 / 2 ^ 64) + (xl5 * ul1 / 2 ^ 64) + (xl4 * ul2 / 2 ^ 64) + (xl3 * ul3 / 2 ^ 64)) +
      2 ^ 256 * (xl7 * ul0 + xl6 * ul1 + xl5 * ul2 + xl4 * ul3 + xl3 * ul4) +
      2 ^ 320 * (xl7 * ul1 + xl6 * ul2 + xl5 * ul3 + xl4 * ul4) +
      2 ^ 384 * (xl7 * ul2 + xl6 * ul3 + xl5 * ul4) +
      2 ^ 448 * (xl7 * ul3 + xl6 * ul4) +
      2 ^ 512 * (xl7 * ul4))
    (hq : V = T / 2 ^ 320)
    (hbl : Bl = (V * (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3)) % 2 ^ 320)
    (hs1 : r8 = 0 ↔ Bl ≤ xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4)
    (hs2 : r8 = 0 → D + Bl = xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4)
    (hs3 : r8 ≠ 0 → D + Bl = xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4 + 2 ^ 320)
    (hf0 : r8 = 0 → C = D)
    (hf1 : r8 ≠ 0 → C = (D + (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3)) % 2 ^ 320) :
    C % (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3) =
      (xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4 + 2 ^ 320 * xl5 + 2 ^ 384 * xl6 + 2 ^ 448 * xl7) %
        (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3) ∧
    C < 2 ^ 128 * (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3) + (ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3) := by
  obtain ⟨x, hx⟩ : ∃ x, x = xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4 + 2 ^ 320 * xl5 + 2 ^ 384 * xl6 + 2 ^ 448 * xl7 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ml0 + 2 ^ 64 * ml1 + 2 ^ 128 * ml2 + 2 ^ 192 * ml3 := ⟨_, rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu, mu = ul0 + 2 ^ 64 * ul1 + 2 ^ 128 * ul2 + 2 ^ 192 * ul3 + 2 ^ 256 * ul4 := ⟨_, rfl⟩
  rw [← hx, ← hm]
  rw [← hm, ← hmu] at hmuw
  have hxlt : x < 2 ^ 512 := by rw [hx]; omega
  have hm1 : 2 ^ 192 ≤ m := by rw [hm]; omega
  have hm2 : m < 2 ^ 256 := by rw [hm]; omega
  have ha : x / 2 ^ 192 = xl3 + 2 ^ 64 * xl4 + 2 ^ 128 * xl5 + 2 ^ 192 * xl6 + 2 ^ 256 * xl7 := by rw [hx]; omega
  have hA : xl0 + 2 ^ 64 * xl1 + 2 ^ 128 * xl2 + 2 ^ 192 * xl3 + 2 ^ 256 * xl4 = x % 2 ^ 320 := by rw [hx]; omega
  have hqq := q_ok x mu T xl3 xl4 xl5 xl6 xl7 ul0 ul1 ul2 ul3 ul4 bx3 bx4 bx5 bx6 bx7 bu0 bu1 bu2 bu3 bu4 ha hmu hT
  rw [← hq] at hqq
  obtain ⟨hr1, hr2⟩ := reduce_value x m mu V hxlt hm1 hm2 hmuw hqq.1 hqq.2
  rw [← hm] at hbl
  have hC := r_ok x m V _ Bl D C r8 hA hbl hr1 hs1 hs2 hs3 hf0 (by rw [← hm] at hf1; exact hf1)
  rw [hC]
  refine ⟨hr2, ?_⟩
  rw [hC] at *
  have : (2 : Nat) ^ 320 ≤ 2 ^ 128 * m := by
    calc (2 : Nat) ^ 320 = 2 ^ 128 * 2 ^ 192 := by rw [← Nat.pow_add]
      _ ≤ 2 ^ 128 * m := Nat.mul_le_mul_left _ hm1
  omega

end Fv256.Arm64.R4Nat
