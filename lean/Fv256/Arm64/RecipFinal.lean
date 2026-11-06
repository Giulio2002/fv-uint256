import Fv256.Arm64.RecipArith5c
import Fv256.Arm64.RecipBridge
import Fv256.Arm64.RecipPaths

namespace Fv256.Arm64.RecipSeg
open Fv256.F Fv256.RecipMath Fv256.Arm64.RecipBridge

/-- the pure-`Nat` end of the main path: the values the machine stages leave behind give `recipModel` -/
theorem chain_final64 (m0 m1 m2 m3 y0 y1 y2 y3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0)
    (cy0 : y0 < 2 ^ 64) (cy1 : y1 < 2 ^ 64) (cy2 : y2 < 2 ^ 64) (cy3 : y3 < 2 ^ 64)
    (hY : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 =
      Fv256.Spec.lsh (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) (Janus.Arm64.clzNat 64 m3))
    (r1 : Nat) (hr1 : r1 = recipR1 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3))
    (r2 : Nat) (hr2 : r2 = (if ((2 * (r1 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e r1 y2 y3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ 2 * y3 % 2 ^ 64 = 0)
        then 2 ^ 128 - 1 else (2 * (r1 * 2 ^ 64) + 2 ^ 128 - (2 * stage2e r1 y2 y3) % 2 ^ 128) % 2 ^ 128))
    (r3 : Nat) (hr3 : r3 = 2 * ((((r2) * 2 ^ 192 + 2 ^ 320 - stage3q (rsqw r2 0) (rsqw r2 1) (rsqw r2 2) (rsqw r2 3) y0 y1 y2 y3) % 2 ^ 320) / 2 ^ 128) % 2 ^ 192)
    (p : Nat) (hp : p = (r3 * 2 ^ 256 + 2 ^ 448 - v4g (rsqw r3 0) (rsqw r3 1) (rsqw r3 2) (rsqw r3 3) (rsqw r3 4) (rsqw r3 5) y0 y1 y2 y3) % 2 ^ 448 / 2 ^ 128)
    (f : Nat) (hf : f = if 2 ^ 574 < p * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) then 1 else 0)
    (sidx m176 : Nat) (hs : sidx = 255 - Janus.Arm64.clzNat 64 m3) (hm : m176 = (18446744073709551615 + sidx % 64) % 18446744073709551616)
    (S : Nat) (hS : S = (if 2 ^ 63 ≤ m176 then 2 * (if f = 0 then p else (p + 2 ^ 320 - 1) % 2 ^ 320) % 2 ^ 320 else (if f = 0 then p else (p + 2 ^ 320 - 1) % 2 ^ 320) / 2 ^ m176)) :
    S = recipTail (recipS (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3)) (recipR4 (recipY (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3))) := by
  have hYm := lsh_eq_recipY m0 m1 m2 m3 b0 b1 b2 b3 h3
  have hsS := recipS_eq m0 m1 m2 m3 b0 b1 b2 b3 h3
  have hYv : recipY (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) = y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 := by
    rw [← hYm, ← hY]
  rw [hsS, hYv]
  obtain ⟨w0, w1, w2, w3⟩ := yw_words y0 y1 y2 y3 cy0 cy1 cy2 cy3
  have e2 : r2 = recipR2 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR2 recipR2raw
    rw [w2, w3, ← hr1]
    exact hr2
  have e3 : r3 = recipR3 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR3 recipQ3
    rw [← e2, w0, w1, w2, w3]
    exact hr3
  have e4 : p = recipR4pre (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR4pre recipV4
    rw [← e3, w0, w1, w2, w3]
    exact hp
  have e5 : (if f = 0 then p else (p + 2 ^ 320 - 1) % 2 ^ 320) = recipR4 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR4
    rw [← e4, hf]
    split <;> simp_all
  have hc : Janus.Arm64.clzNat 64 m3 ≤ 63 := Fv256.Arm64.RecipNat.clz_le _ b3 h3
  rw [hS, e5]
  by_cases hle : Janus.Arm64.clzNat 64 m3 ≤ 62
  · have hr : m176 = 62 - Janus.Arm64.clzNat 64 m3 := by rw [hm, hs]; omega
    have hnn : ¬ 2 ^ 63 ≤ m176 := by omega
    rw [if_neg hnn, hr]
    unfold recipTail
    rw [if_pos hle]
  · have hc63 : Janus.Arm64.clzNat 64 m3 = 63 := by omega
    have hr : m176 = 18446744073709551615 := by rw [hm, hs, hc63]
    have hnn : 2 ^ 63 ≤ m176 := by omega
    rw [if_pos hnn]
    unfold recipTail
    rw [if_neg hle]

end Fv256.Arm64.RecipSeg
