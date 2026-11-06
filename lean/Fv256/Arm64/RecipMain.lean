import Fv256.Arm64.RecipFinal
import Fv256.Arm64.RecipG.C_88_108
import Fv256.Arm64.RecipG.G_108_16c
import Fv256.Arm64.RecipG.C_16c_284
import Fv256.Arm64.RecipG.C_284_390
import Fv256.Arm64.RecipG.C_390_4a8
import Fv256.Arm64.RecipG.C_4a8_564
import Fv256.Arm64.RecipG.C_564_698
import Fv256.Arm64.RecipG.C_698_77c
import Fv256.Arm64.RecipArith1
import Fv256.Arm64.RecipArith2

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg
open Fv256.F Fv256.RecipMath

theorem lt_reg {S : State} {i : Nat} {v : Nat} (h : (S.regs i).toNat = v) : v < 2 ^ 64 := h ▸ BitVec.isLt _
theorem lt_mem {M : Memory} {a v : Nat} (h : M.readLE a 8 = v) : v < 2 ^ 64 := h ▸ Util.readLE8_lt _ _

theorem spo (x y : Nat) (h : y + 272 = x) :
    x + 8 = y + 280 ∧ x + 8 + 8 = y + 288 ∧ x + 8 + 16 = y + 296 ∧ x + 8 + 24 = y + 304 ∧ x + 8 + 32 = y + 312 := by
  omega

theorem m176_cases (c : Nat) (hc : c ≤ 63) : (18446744073709551615 + (255 - c) % 64) % 18446744073709551616 < 64 ∨ 2 ^ 63 ≤ (18446744073709551615 + (255 - c) % 64) % 18446744073709551616 := by
  omega

theorem pow2_nat (m0 m1 m2 m3 : Nat) (b0 : m0 < 2 ^ 64) (b1 : m1 < 2 ^ 64) (b2 : m2 < 2 ^ 64) (b3 : m3 < 2 ^ 64) (h3 : m3 ≠ 0) :
    ((m3 &&& m3 - 1 ||| (m2 ||| (m1 ||| m0))) = 0) ↔
      (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3 = 2 ^ Nat.log2 (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2 + 2 ^ 192 * m3)) := by
  rw [← Fv256.F.pow2_limbs m0 m1 m2 m3 b0 b1 b2 b3 h3]
  simp only [Nat.or_eq_zero_iff]
  constructor
  · rintro ⟨h4, h2, h1, h0⟩; exact ⟨⟨⟨h0, h1⟩, h2⟩, h4⟩
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h4⟩; exact ⟨h4, h2, h1, h0⟩

theorem m_limbs (s : State) :
    s.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 0).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 0).toNat + 8) 8 +
      2 ^ 128 * s.mem.readLE ((s.regs 0).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 0).toNat + 24) 8 := Util.readLE_32 _ _

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem main_path (s : State) (hpc : s.pc = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hz : ¬ (s.mem.readLE ((s.regs 0).toNat + 24) 8 &&& s.mem.readLE ((s.regs 0).toNat + 24) 8 - 1 |||
      (s.mem.readLE ((s.regs 0).toNat + 16) 8 ||| (s.mem.readLE ((s.regs 0).toNat + 8) 8 ||| s.mem.readLE (s.regs 0).toNat 8))) = 0) :
    ReachesRet Fv256.Arm64.RecipProg.program (s.regs 30) s (fun s' => RecPost s s' (Fv256.F.recipModel (s.mem.readLE (s.regs 0).toNat 32))) := by
  have hpre' := hpre
  have hs280 : 280 ≤ s.sp.toNat := hpre.2.2.2.1.2.1
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hm192 : ¬ (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192) := by
    rw [m_limbs s]
    have : 0 < s.mem.readLE ((s.regs 0).toNat + 24) 8 := Nat.pos_of_ne_zero hm3
    omega
  refine Fv256.Arm64.SegCompose.seg_trans (seg0 s hpc hpre hm3 hz) ?_
  intro S1 hpc1 hq1
  obtain ⟨y0, y1, y2, y3, sidx, hL1, hYl, hsidx, h63, hR1, hM1⟩ := hq1
  unfold mval mw at hYl
  unfold mw at hsidx
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl] at hYl hsidx
  have hL1' := hL1
  obtain ⟨c0, c1, c2, c3, c4⟩ := hL1'
  have by0 := lt_mem c0
  have by1 := lt_mem c1
  have by2 := lt_mem c2
  have by3 := lt_mem c3
  refine Fv256.Arm64.SegCompose.seg_trans (c_88_108 s S1 hpc1 hpre hR1 hM1 y0 y1 y2 y3 sidx hL1 h63) ?_
  intro S2 hpc2 hq2
  obtain ⟨r1, m176, hL2, hr1, hm176, hR2, hM2⟩ := sum1 s S2 y0 y1 y2 y3 sidx hq2 by0 by1 by2 by3 h63
  have hL2' := hL2
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hL2'
  have br1 := lt_reg d0
  refine Fv256.Arm64.SegCompose.seg_trans (g_108_16c s S2 hpc2 hpre hR2 hM2 r1 18446744073709551615 y2 y3 y0 y1 m176 y0 y1 y2 hL2) ?_
  intro S3 hpc3 hq3
  obtain ⟨r0, r7, hL3, hr2, hR3, hM3⟩ := sum2 s S3 r1 18446744073709551615 y2 y3 y0 y1 m176 y0 y1 y2 hq3 br1 rfl by2 by3
  have hL3' := hL3
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := hL3'
  have br0 := lt_reg f0
  have br7 := lt_reg f5
  refine Fv256.Arm64.SegCompose.seg_trans (c_16c_284 s S3 hpc3 hpre hR3 hM3 r0 y2 y3 y0 y1 r7 0 m176 y0 y1 y2 hL3) ?_
  intro S4 hpc4 hq4
  obtain ⟨x284r0, x284r1, x284r2, m128, m136, hL4, e128, e136, hr3, hR4, hM4⟩ := sum3 s S4 r0 y2 y3 y0 y1 r7 0 m176 y0 y1 y2 hq4 br0 by2 by3 by0 by1 br7 rfl
  have hL4' := hL4
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hL4'
  have bx0 := lt_reg g0
  have bx1 := lt_reg g1
  have bx2 := lt_reg g2
  refine Fv256.Arm64.SegCompose.seg_trans (c_284_390 s S4 hpc4 hpre hR4 hM4 x284r0 x284r1 x284r2 y3 0 m128 m136 m176 y0 y1 y2 hL4) ?_
  intro S5 hpc5 hq5
  unfold PC_284_390 at hq5
  obtain ⟨x2a8r4, x2a8r5, x2a8r6, x2a8r7, x2a8r8, x2a8r9, x2a8r11, x2a8r12, x2fcr5, x2fcr6, x2fcr7, x2fcr8, x2fcr9, x2fcm112, x2fcm120, x334r12, x334r13, x334r14, x334r15, x334r16, x334r19, x334r21, x334r22, x334r23, x334r24, x334r25, x334r26, x370r0, x370r1, x370r2, x370r4, x370r20, x370r30, x370m72, x370m216, x370m224, x370m232, x390r5, x390r7, x390r11, x390r17, x390m200, x390m208, hqq⟩ := hq5
  obtain ⟨hL5, h_x2a8r4, h_x2a8r5, h_x2a8r6, h_x2a8r7, h_x2a8r8, h_x2a8r9, h_x2a8r11, h_x2a8r12, h_x2fcr5, h_x2fcr6, h_x2fcr7, h_x2fcr8, h_x2fcr9, h_x2fcm112, h_x2fcm120, h_x334r12, h_x334r13, h_x334r14, h_x334r15, h_x334r16, h_x334r19, h_x334r21, h_x334r22, h_x334r23, h_x334r24, h_x334r25, h_x334r26, h_x370r0, h_x370r1, h_x370r2, h_x370r4, h_x370r20, h_x370r30, h_x370m72, h_x370m216, h_x370m224, h_x370m232, h_x390r5, h_x390r7, h_x390r11, h_x390r17, h_x390m200, h_x390m208, hR5, hM5⟩ := hqq
  refine Fv256.Arm64.SegCompose.seg_trans (c_390_4a8 s S5 hpc5 hpre hR5 hM5 x370r0 x370r1 x370r2 y3 x370r4 x390r5 x2fcr6 x390r7 x2fcr8 x2fcr9 0 x390r11 x334r12 x334r13 x334r14 x334r15 x334r16 x390r17 x334r19 x370r20 x334r21 x334r22 x334r23 x334r24 x334r25 x334r26 x370r30 x370m72 x2fcm112 x2fcm120 m128 m136 x284r0 m176 x390m200 x390m208 x370m216 x370m224 x370m232 y0 y1 y2 hL5) ?_
  intro S6 hpc6 hq6
  unfold PC_390_4a8 at hq6
  obtain ⟨x3d0r6, x3d0r7, x3d0r8, x3d0r9, x3d0r13, x3d0r14, x3d0r15, x3d0r16, x3d0m64, x3d0m184, x404r0, x404r1, x404r2, x404r4, x404r12, x404r13, x448r1, x448r2, x448r4, x448r5, x448r7, x448r11, x470r0, x470r1, x470r2, x470r4, x470r5, x470r6, x470r7, x4a8r0, x4a8r1, x4a8r2, x4a8r4, x4a8r5, x4a8m80, x4a8m88, x4a8m96, x4a8m104, hqq⟩ := hq6
  obtain ⟨hL6, h_x3d0r6, h_x3d0r7, h_x3d0r8, h_x3d0r9, h_x3d0r13, h_x3d0r14, h_x3d0r15, h_x3d0r16, h_x3d0m64, h_x3d0m184, h_x404r0, h_x404r1, h_x404r2, h_x404r4, h_x404r12, h_x404r13, h_x448r1, h_x448r2, h_x448r4, h_x448r5, h_x448r7, h_x448r11, h_x470r0, h_x470r1, h_x470r2, h_x470r4, h_x470r5, h_x470r6, h_x470r7, h_x4a8r0, h_x4a8r1, h_x4a8r2, h_x4a8r4, h_x4a8r5, h_x4a8m80, h_x4a8m88, h_x4a8m96, h_x4a8m104, hR6, hM6⟩ := hqq
  obtain ⟨hp4, hm80, hm88, hm96, hm104⟩ := sum4 x284r0 x284r1 x284r2 y3 0 m128 m136 m176 y0 y1 y2 x2a8r4 x2a8r5 x2a8r6 x2a8r7 x2a8r8 x2a8r9 x2a8r11 x2a8r12 x2fcr5 x2fcr6 x2fcr7 x2fcr8 x2fcr9 x2fcm112 x2fcm120 x334r12 x334r13 x334r14 x334r15 x334r16 x334r19 x334r21 x334r22 x334r23 x334r24 x334r25 x334r26 x370r0 x370r1 x370r2 x370r4 x370r20 x370r30 x370m72 x370m216 x370m224 x370m232 x390r5 x390r7 x390r11 x390r17 x390m200 x390m208 x3d0r6 x3d0r7 x3d0r8 x3d0r9 x3d0r13 x3d0r14 x3d0r15 x3d0r16 x3d0m64 x3d0m184 x404r0 x404r1 x404r2 x404r4 x404r12 x404r13 x448r1 x448r2 x448r4 x448r5 x448r7 x448r11 x470r0 x470r1 x470r2 x470r4 x470r5 x470r6 x470r7 x4a8r0 x4a8r1 x4a8r2 x4a8r4 x4a8r5 x4a8m80 x4a8m88 x4a8m96 x4a8m104 bx0 bx1 bx2 by3 rfl by0 by1 by2 e128 e136 h_x2a8r4 h_x2a8r5 h_x2a8r6 h_x2a8r7 h_x2a8r8 h_x2a8r9 h_x2a8r11 h_x2a8r12 h_x2fcr5 h_x2fcr6 h_x2fcr7 h_x2fcr8 h_x2fcr9 h_x2fcm112 h_x2fcm120 h_x334r12 h_x334r13 h_x334r14 h_x334r15 h_x334r16 h_x334r19 h_x334r21 h_x334r22 h_x334r23 h_x334r24 h_x334r25 h_x334r26 h_x370r0 h_x370r1 h_x370r2 h_x370r4 h_x370r20 h_x370r30 h_x370m72 h_x370m216 h_x370m224 h_x370m232 h_x390r5 h_x390r7 h_x390r11 h_x390r17 h_x390m200 h_x390m208 h_x3d0r6 h_x3d0r7 h_x3d0r8 h_x3d0r9 h_x3d0r13 h_x3d0r14 h_x3d0r15 h_x3d0r16 h_x3d0m64 h_x3d0m184 h_x404r0 h_x404r1 h_x404r2 h_x404r4 h_x404r12 h_x404r13 h_x448r1 h_x448r2 h_x448r4 h_x448r5 h_x448r7 h_x448r11 h_x470r0 h_x470r1 h_x470r2 h_x470r4 h_x470r5 h_x470r6 h_x470r7 h_x4a8r0 h_x4a8r1 h_x4a8r2 h_x4a8r4 h_x4a8r5 h_x4a8m80 h_x4a8m88 h_x4a8m96 h_x4a8m104
  have hL6' := hL6
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ := hL6'
  have bp0 := lt_reg k0
  have bp1 := lt_reg k1
  have bp2 := lt_reg k2
  have bp4 := lt_reg k4
  have bp5 := lt_reg k5
  refine Fv256.Arm64.SegCompose.seg_trans (c_4a8_564 s S6 hpc6 hpre hR6 hM6 x4a8r0 x4a8r1 x4a8r2 y3 x4a8r4 x4a8r5 0 x4a8m80 x4a8m88 x4a8m96 x4a8m104 m176 y0 y1 y2 hL6) ?_
  intro S7 hpc7 hq7
  unfold PC_4a8_564 at hq7
  obtain ⟨x4c4r8, x4c4r9, x4c4r11, x4c4r12, x4c4m168, x4e4r6, x4e4r13, x4e4r14, x4e4r15, x4e4r16, x4e4r19, x4e4r20, x504r17, x504r21, x504r22, x504r23, x504r24, x504r25, x504r26, x504r30, x524m120, x524m248, x524m256, x544m160, x544m224, x544m232, x544m240, x564r7, x564r17, x564m200, x564m208, x564m216, hqq⟩ := hq7
  obtain ⟨hL7, h_x4c4r8, h_x4c4r9, h_x4c4r11, h_x4c4r12, h_x4c4m168, h_x4e4r6, h_x4e4r13, h_x4e4r14, h_x4e4r15, h_x4e4r16, h_x4e4r19, h_x4e4r20, h_x504r17, h_x504r21, h_x504r22, h_x504r23, h_x504r24, h_x504r25, h_x504r26, h_x504r30, h_x524m120, h_x524m248, h_x524m256, h_x544m160, h_x544m224, h_x544m232, h_x544m240, h_x564r7, h_x564r17, h_x564m200, h_x564m208, h_x564m216, hR7, hM7⟩ := hqq
  refine Fv256.Arm64.SegCompose.seg_trans (c_564_698 s S7 hpc7 hpre hR7 hM7 x4a8r1 x4a8r2 y3 x4a8r4 x4a8r5 x4e4r6 x564r7 x4c4r8 x4c4r9 0 x4c4r11 x4c4r12 x4e4r13 x4e4r14 x4e4r15 x4e4r16 x564r17 x4e4r19 x4e4r20 x504r21 x504r22 x504r23 x504r24 x504r25 x504r26 x504r30 x4a8m80 x4a8m88 x4a8m96 x4a8m104 x504r17 x524m120 x544m160 x4c4m168 m176 x564m200 x564m208 x564m216 x544m224 x544m232 x544m240 x524m248 x524m256 hL7) ?_
  intro S8 hpc8 hq8
  unfold PC_564_698 at hq8
  obtain ⟨x5a4r0, x5a4r1, x5a4r2, x5a4r3, x5a4r5, x5a4r6, x5a4r8, x5a4r9, x5a4r11, x5a4r12, x5a4m152, x5a4m184, x5a4m192, x5d4r6, x5d4r8, x5d4r9, x5d4r11, x5d4r12, x5d4r13, x604r6, x604r9, x604r11, x604r12, x604r13, x604r14, x648r0, x648r2, x648r6, x648r7, x648r11, x648r12, x698r0, hqq⟩ := hq8
  obtain ⟨hL8, h_x5a4r0, h_x5a4r1, h_x5a4r2, h_x5a4r3, h_x5a4r5, h_x5a4r6, h_x5a4r8, h_x5a4r9, h_x5a4r11, h_x5a4r12, h_x5a4m152, h_x5a4m184, h_x5a4m192, h_x5d4r6, h_x5d4r8, h_x5d4r9, h_x5d4r11, h_x5d4r12, h_x5d4r13, h_x604r6, h_x604r9, h_x604r11, h_x604r12, h_x604r13, h_x604r14, h_x648r0, h_x648r2, h_x648r6, h_x648r7, h_x648r11, h_x648r12, h_x698r0, hR8, hM8⟩ := hqq
  have hflag := sum5a x4a8r0 x4a8r1 x4a8r2 y3 x4a8r4 x4a8r5 x4a8m80 x4a8m88 x4a8m96 x4a8m104 m176 y0 y1 y2 x4c4r8 x4c4r9 x4c4r11 x4c4r12 x4c4m168 x4e4r6 x4e4r13 x4e4r14 x4e4r15 x4e4r16 x4e4r19 x4e4r20 x504r17 x504r21 x504r22 x504r23 x504r24 x504r25 x504r26 x504r30 x524m120 x524m248 x524m256 x544m160 x544m224 x544m232 x544m240 x564r7 x564r17 x564m200 x564m208 x564m216 x5a4r0 x5a4r1 x5a4r2 x5a4r3 x5a4r5 x5a4r6 x5a4r8 x5a4r9 x5a4r11 x5a4r12 x5a4m152 x5a4m184 x5a4m192 x5d4r6 x5d4r8 x5d4r9 x5d4r11 x5d4r12 x5d4r13 x604r6 x604r9 x604r11 x604r12 x604r13 x604r14 x648r0 x648r2 x648r6 x648r7 x648r11 x648r12 x698r0 bp0 bp1 bp2 by3 bp4 bp5 by0 by1 by2 h_x4c4r8 h_x4c4r9 h_x4c4r11 h_x4c4r12 h_x4c4m168 h_x4e4r6 h_x4e4r13 h_x4e4r14 h_x4e4r15 h_x4e4r16 h_x4e4r19 h_x4e4r20 h_x504r17 h_x504r21 h_x504r22 h_x504r23 h_x504r24 h_x504r25 h_x504r26 h_x504r30 h_x524m120 h_x524m248 h_x524m256 h_x544m160 h_x544m224 h_x544m232 h_x544m240 h_x564r7 h_x564r17 h_x564m200 h_x564m208 h_x564m216 h_x5a4r0 h_x5a4r1 h_x5a4r2 h_x5a4r3 h_x5a4r5 h_x5a4r6 h_x5a4r8 h_x5a4r9 h_x5a4r11 h_x5a4r12 h_x5a4m152 h_x5a4m184 h_x5a4m192 h_x5d4r6 h_x5d4r8 h_x5d4r9 h_x5d4r11 h_x5d4r12 h_x5d4r13 h_x604r6 h_x604r9 h_x604r11 h_x604r12 h_x604r13 h_x604r14 h_x648r0 h_x648r2 h_x648r6 h_x648r7 h_x648r11 h_x648r12 h_x698r0
  refine Fv256.Arm64.SegCompose.seg_trans (c_698_77c s S8 hpc8 hpre hR8 hM8 x698r0 x4a8m104 x4a8r4 0 x4a8m80 x4a8m88 x4a8m96 m176 hL8) ?_
  intro S9 hpc9 hq9
  unfold PC_698_77c at hq9
  obtain ⟨x708r0, x708r1, x708r2, x708r3, x708r4, x708r5, x77cm280, x77cm288, x77cm296, x77cm304, x77cm312, hqq⟩ := hq9
  obtain ⟨hL9, h_x708r0, h_x708r1, h_x708r2, h_x708r3, h_x708r4, h_x708r5, h_x77cm280, h_x77cm288, h_x77cm296, h_x77cm304, h_x77cm312, hR9, hM9⟩ := hqq
  have hflag' := hflag
  have hf1 : x698r0 ≤ 1 := by rw [hflag]; split <;> simp
  have hmlt : m176 < 2 ^ 64 := by rw [hm176]; exact Nat.mod_lt _ (by decide)
  have hclz : clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 := Fv256.Arm64.RecipNat.clz_le _ (Util.readLE8_lt _ _) hm3
  have hscase : m176 < 64 ∨ 2 ^ 63 ≤ m176 := by rw [hm176, hsidx]; exact m176_cases _ hclz
  have bw1 : x4a8m104 < 2 ^ 64 := by rw [hm104]; exact bp0
  have bw96 : x4a8m96 < 2 ^ 64 := by rw [hm96]; exact bp1
  have bw88 : x4a8m88 < 2 ^ 64 := by rw [hm88]; exact bp2
  have bw80 : x4a8m80 < 2 ^ 64 := by rw [hm80]; exact bp5
  have h5c := sum5c x698r0 x4a8m104 x4a8r4 x4a8m80 x4a8m88 x4a8m96 m176 x708r0 x708r1 x708r2 x708r3 x708r4 x708r5 x77cm280 x77cm288 x77cm296 x77cm304 x77cm312 bw1 bw96 bw88 bp4 bw80 hf1 hmlt hscase h_x708r0 h_x708r1 h_x708r2 h_x708r3 h_x708r4 h_x708r5 h_x77cm280 h_x77cm288 h_x77cm296 h_x77cm304 h_x77cm312
  rw [hm104, hm96, hm88, hm80] at h5c
  refine Fv256.Arm64.SegCompose.seg_mono (g_epi s S9 hpc9 hpre hR9 hM9) ?_
  intro S' ⟨e1, e2, e3, e4, e5, e6⟩
  have hsp : S9.sp.toNat + 272 = s.sp.toNat := RecRegs.sp_toNat hR9 hs280
  refine ⟨e1, e2, e3, e4, e5, ?_, ?_⟩
  · rw [e6]; exact hM9.2.2
  · rw [e6, readLE_40]
    obtain ⟨u0, u1, u2, u3, u4⟩ := hL9
    obtain ⟨a0, a1, a2, a3, a4⟩ := spo _ _ hsp
    rw [a1, a2, a3, a4, a0, u0, u1, u2, u3, u4, h5c]
    have hpw : ¬ (s.mem.readLE (s.regs 0).toNat 32 = 2 ^ Nat.log2 (s.mem.readLE (s.regs 0).toNat 32)) := by
      intro h
      apply hz
      rw [m_limbs s] at h
      exact (pow2_nat _ _ _ _ bb0 bb1 bb2 bb3 hm3).2 h
    unfold Fv256.F.recipModel
    rw [if_neg hm192, if_neg hpw, m_limbs s]
    have hYl' : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Fv256.Spec.lsh (s.mem.readLE (s.regs 0).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 0).toNat + 8) 8 + 2 ^ 128 * s.mem.readLE ((s.regs 0).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 0).toNat + 24) 8) (clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) := hYl
    exact chain_final64 _ _ _ _ y0 y1 y2 y3 bb0 bb1 bb2 bb3 hm3 by0 by1 by2 by3 hYl' r1 hr1 (r7 + 2 ^ 64 * r0) hr2
      (x284r1 + 2 ^ 64 * x284r2 + 2 ^ 128 * x284r0) hr3 (x4a8r0 + 2 ^ 64 * x4a8r1 + 2 ^ 128 * x4a8r2 + 2 ^ 192 * x4a8r4 + 2 ^ 256 * x4a8r5) hp4
      x698r0 hflag sidx m176 hsidx hm176 _ rfl


end Fv256.Arm64.RecipSeg
