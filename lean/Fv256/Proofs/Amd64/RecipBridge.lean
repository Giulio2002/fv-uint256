import Fv256.Proofs.Amd64.RecipSeg1
import Fv256.Proofs.Amd64.RecipArith2
import Fv256.Proofs.Amd64.RecipArith3
import Fv256.Proofs.Amd64.RecipStage4
import Fv256.Proofs.Amd64.LshNorm
import Fv256.Proofs.Common.RecipChainDefs
import Fv256.Proofs.Common.RecipPow2
import Fv256.Proofs.Common.RecipChain
import Fv256.Proofs.Common.UtilB

/-!
# Bridging lemmas: machine-level stage values = the pure-Nat model `Fv256.F.recipModel`
-/

namespace Fv256.Amd64.RecipSeg
open Fv256.F Fv256.RecipMath

theorem yw_words (y0 y1 y2 y3 : Nat) (b0 : y0 < 2 ^ 64) (b1 : y1 < 2 ^ 64) (b2 : y2 < 2 ^ 64) (b3 : y3 < 2 ^ 64) :
    yw (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) 0 = y0 ∧
    yw (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) 1 = y1 ∧
    yw (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) 2 = y2 ∧
    yw (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) 3 = y3 := by
  unfold yw
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | omega | (simp only [Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one]; omega)

/-- stage 1: `r1` after the `cmove` -/
theorem r1_bridge (Y y3 ax dx : Nat) (h3 : yw Y 3 = y3) (h63 : 2 ^ 63 ≤ y3) (hlt : y3 < 2 ^ 64)
    (hax : ax = r1rawf y3 % 18446744073709551616) (hdx : dx = (ax ||| 2 * y3 % 18446744073709551616)) :
    r1c ax dx = recipR1 Y := by
  have hr0 : recipR0 Y = r0f y3 := by unfold recipR0 r0f; rw [h3]
  have hlt0 := r0f_lt y3 h63 hlt
  have hsq : r0f y3 * r0f y3 < 2 ^ 64 := by
    have : r0f y3 * r0f y3 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hlt0 hlt0
    simpa [← Nat.pow_add] using this
  have hT1 : recipT1 Y = t1f y3 := by
    unfold recipT1 t1f; rw [h3, hr0, Nat.mod_eq_of_lt hsq]
  have hle := t1f_le y3 h63 hlt
  have hraw : recipR1raw Y = ax := by
    unfold recipR1raw; rw [hr0, hT1, hax]; unfold r1rawf
    have : (r0f y3 * 2 ^ 32 + 2 ^ 64 - t1f y3) % 2 ^ 64 = r0f y3 * 2 ^ 32 - t1f y3 := by
      have : r0f y3 * 2 ^ 32 < 2 ^ 64 := by omega
      omega
    rw [this]
  unfold r1c recipR1
  rw [hraw, h3, hdx]

/-- the position of the top bit of `m` -/
theorem log2_split (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0) :
    Nat.log2 (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) = 192 + Nat.log2 m3 := by
  have hm : m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 ≠ 0 := by
    have : 0 < m3 := Nat.pos_of_ne_zero h3
    omega
  rw [Nat.log2_eq_iff hm]
  have l1 : 2 ^ Nat.log2 m3 ≤ m3 := Nat.log2_self_le h3
  have l2 : m3 < 2 ^ (Nat.log2 m3 + 1) := Nat.lt_log2_self
  have e1 : 2 ^ (192 + Nat.log2 m3) = 2 ^ 192 * 2 ^ Nat.log2 m3 := Nat.pow_add _ _ _
  have e2 : 2 ^ (192 + Nat.log2 m3 + 1) = 2 ^ 192 * 2 ^ (Nat.log2 m3 + 1) := by rw [Nat.add_assoc, Nat.pow_add]
  rw [e1, e2]
  constructor
  · have := Nat.mul_le_mul_left (2 ^ 192) l1
    omega
  · have := Nat.mul_lt_mul_of_pos_left l2 (Nat.two_pow_pos 192)
    have : 2 ^ 128 * m2 + 2 ^ 64 * m1 + m0 < 2 ^ 192 := by omega
    omega

theorem clz_log2 (m3 : Nat) (h : m3 < 2 ^ 64) (h0 : m3 ≠ 0) : Janus.Arm64.clzNat 64 m3 = 63 - Nat.log2 m3 := by
  have hc := Fv256.Util.clz_bl 64 m3 h
  have hbl : Fv256.Spec.bitLen m3 = Nat.log2 m3 + 1 := by unfold Fv256.Spec.bitLen; rw [if_neg h0]
  have hlog : Nat.log2 m3 < 64 := by rw [Nat.log2_lt h0]; exact h
  omega

theorem recipS_eq (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0) :
    recipS (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) = Janus.Arm64.clzNat 64 m3 := by
  have hlog : Nat.log2 m3 < 64 := by rw [Nat.log2_lt h3]; exact b3
  unfold recipS
  rw [log2_split m0 m1 m2 m3 b0 b1 b2 b3 h3, clz_log2 m3 b3 h3]
  omega

theorem lsh_eq_recipY (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0) :
    Fv256.Spec.lsh (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) (Janus.Arm64.clzNat 64 m3) =
      recipY (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) := by
  unfold Fv256.Spec.lsh recipY
  rw [recipS_eq m0 m1 m2 m3 b0 b1 b2 b3 h3]
  apply Nat.mod_eq_of_lt
  have hlog : Nat.log2 m3 < 64 := by rw [Nat.log2_lt h3]; exact b3
  have hc := clz_log2 m3 b3 h3
  have hl : m3 < 2 ^ (Nat.log2 m3 + 1) := Nat.lt_log2_self
  have hm : m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 < 2 ^ 192 * 2 ^ (Nat.log2 m3 + 1) := by
    have := Nat.mul_lt_mul_of_pos_left hl (Nat.two_pow_pos 192)
    omega
  have e : 2 ^ 192 * 2 ^ (Nat.log2 m3 + 1) * 2 ^ (63 - Nat.log2 m3) = 2 ^ 256 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [hc]
  calc _ < 2 ^ 192 * 2 ^ (Nat.log2 m3 + 1) * 2 ^ (63 - Nat.log2 m3) := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ = _ := e

theorem pow2_test (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0) :
    ((BitVec.ofNat 64 m3 - 1#64 &&& BitVec.ofNat 64 m3 ||| (BitVec.ofNat 64 m0 ||| BitVec.ofNat 64 m1 ||| BitVec.ofNat 64 m2)).toNat = 0) ↔
      (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 = 2 ^ Nat.log2 (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3)) := by
  rw [← Fv256.F.pow2_limbs m0 m1 m2 m3 b0 b1 b2 b3 h3]
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3]
  have e : (2 ^ 64 - 1 % 2 ^ 64 + m3) % 2 ^ 64 = m3 - 1 := by
    have : 0 < m3 := Nat.pos_of_ne_zero h3
    omega
  rw [e, Nat.and_comm (m3 - 1) m3, Nat.or_comm]

/-- the whole main path in pure `Nat`: the values the stages leave behind, in the exact form the stage lemmas export, give `recipModel` -/
theorem chain_final (m0 m1 m2 m3 y0 y1 y2 y3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0)
    (cy0 : y0 < 2 ^ 64) (cy1 : y1 < 2 ^ 64) (cy2 : y2 < 2 ^ 64) (cy3 : y3 < 2 ^ 64) (h63 : 2 ^ 63 ≤ y3)
    (hY : y0 + 18446744073709551616 * y1 + 18446744073709551616 ^ 2 * y2 + 18446744073709551616 ^ 3 * y3 =
      Fv256.Spec.lsh (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) (Janus.Arm64.clzNat 64 m3))
    (ax bx dx : Nat) (hax : ax = r1rawf y3 % 18446744073709551616) (hbx : bx = 2 * y3 % 18446744073709551616) (hdx : dx = (ax ||| bx))
    (r2lo r2hi : Nat)
    (hR2 : r2lo + 18446744073709551616 * r2hi =
      (if ((2 * (r1c ax dx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c ax dx) y2 y3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ bx = 0) then 2 ^ 128 - 1
        else (2 * (r1c ax dx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c ax dx) y2 y3) % 2 ^ 128) % 2 ^ 128))
    (r3a r3b r3c : Nat)
    (hR3 : r3a + 2 ^ 64 * r3b + 2 ^ 128 * r3c =
      2 * ((((r2lo + 2 ^ 64 * r2hi) * 2 ^ 192 + 2 ^ 320 - (stage3q (sqw (r2lo + 2 ^ 64 * r2hi) 0) (sqw (r2lo + 2 ^ 64 * r2hi) 1)
        (sqw (r2lo + 2 ^ 64 * r2hi) 2) (sqw (r2lo + 2 ^ 64 * r2hi) 3) y0 y1 y2 y3)) % 2 ^ 320) / 2 ^ 128) % 2 ^ 192)
    (p0 p1 p2 p3 p4 : Nat)
    (hP : p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4 = r4preF (r3a + 2 ^ 64 * r3b + 2 ^ 128 * r3c) y0 y1 y2 y3)
    (rcx0 x14crcx n v : Nat)
    (hrcx : rcx0 = (x14crcx % 64 + 18446744073709551615) % 18446744073709551616)
    (hx14 : x14crcx = (63 - Janus.Arm64.clzNat 64 m3 + 192) % 18446744073709551616)
    (hn : n = (if 2 ^ 63 ≤ rcx0 then 0 else rcx0))
    (Wd : Nat) (hWd : Wd = (if 2 ^ 574 < (p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3)
        then ((p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4) + 2 ^ 320 - 1) % 2 ^ 320
        else (p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4)))
    (hv : v = (if 2 ^ 63 ≤ rcx0 then 2 * Wd % 2 ^ 320 else Wd)) :
    v / 2 ^ n = recipTail (recipS (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3)) (recipR4 (recipY (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3))) := by
  subst hbx
  have hYm := lsh_eq_recipY m0 m1 m2 m3 b0 b1 b2 b3 h3
  have hs := recipS_eq m0 m1 m2 m3 b0 b1 b2 b3 h3
  have hYv : recipY (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3) = y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 := by
    rw [← hYm, ← hY]
  rw [hs, hYv]
  obtain ⟨w0, w1, w2, w3⟩ := yw_words y0 y1 y2 y3 cy0 cy1 cy2 cy3
  have h1 : r1c ax dx = recipR1 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) :=
    r1_bridge _ y3 ax dx w3 h63 cy3 hax hdx
  have h2 : r2lo + 18446744073709551616 * r2hi = recipR2 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR2 recipR2raw
    rw [w2, w3, ← h1]
    exact hR2
  have h3' : r3a + 2 ^ 64 * r3b + 2 ^ 128 * r3c = recipR3 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR3 recipQ3
    rw [← h2, w0, w1, w2, w3]
    exact hR3
  have h4 : p0 + 2 ^ 64 * p1 + 2 ^ 128 * p2 + 2 ^ 192 * p3 + 2 ^ 256 * p4 = recipR4pre (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR4pre recipV4
    rw [← h3', w0, w1, w2, w3]
    unfold r4preF stage4T at hP
    exact hP
  have h5 : Wd = recipR4 (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) := by
    unfold recipR4
    rw [← h4]
    exact hWd
  have hc : Janus.Arm64.clzNat 64 m3 ≤ 63 := Fv256.Amd64.LshNorm.clz_le _ b3 h3
  by_cases hle : Janus.Arm64.clzNat 64 m3 ≤ 62
  · have hr : rcx0 = 62 - Janus.Arm64.clzNat 64 m3 := by rw [hrcx, hx14]; omega
    have hnn : ¬ 2 ^ 63 ≤ rcx0 := by omega
    rw [hv, hn, if_neg hnn, if_neg hnn, hr, h5]
    unfold recipTail
    rw [if_pos hle]
  · have hc63 : Janus.Arm64.clzNat 64 m3 = 63 := by omega
    have hr : rcx0 = 18446744073709551615 := by rw [hrcx, hx14, hc63]
    have hnn : 2 ^ 63 ≤ rcx0 := by omega
    rw [hv, hn, if_pos hnn, if_pos hnn, h5]
    unfold recipTail
    rw [if_neg hle]
    simp

end Fv256.Amd64.RecipSeg
