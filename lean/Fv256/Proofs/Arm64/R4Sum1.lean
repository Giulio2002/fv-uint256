import Fv256.Proofs.Arm64.R4Q
import Fv256.Proofs.Arm64.R4G.G_20_114
import Fv256.Proofs.Arm64.R4G.G_114_120
import Fv256.Proofs.Arm64.R4G.G_120_12c
import Fv256.Proofs.Arm64.R4G.G_12c_138
import Fv256.Proofs.Arm64.R4G.G_138_148
import Fv256.Proofs.Arm64.R4G.G_148_158
import Fv256.Proofs.Arm64.R4G.G_158_16c
import Fv256.Proofs.Arm64.R4G.G_16c_18c
import Fv256.Proofs.Arm64.R4G.G_18c_1b8
import Fv256.Proofs.Arm64.R4G.G_1b8_1d8

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec Fv256.Arm64.R4Nat

namespace Fv256.Arm64.R4Seg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem c_stage1 (s S : State) (hpc : S.pc = BitVec.ofNat 64 (r4Entry + 0x20)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x20r1 x20r2 x20r3 : Nat) (hL : L20 S x20r1 x20r2 x20r3) (hX0 : x20r1 = (s.regs 1).toNat) (hX1 : x20r2 = (s.regs 2).toNat) (hX2 : x20r3 = (s.regs 3).toNat) :
    ReachesRet Fv256.Arm64.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x1d8)) S (fun S1 => ∃ x114r1 x114r2 x114r5 x114m64 x114m72 x114m8 x114m16 x114m24 x114m32 x114m120 x1d8r3 x1d8r4 x1d8r6 x1d8r7 x1d8r9 : Nat,
        L1d8 S1 x114r1 x114r2 x1d8r3 x1d8r4 x114r5 x1d8r6 x1d8r7 x1d8r9 x114m8 x114m16 x114m24 x114m32 x114m64 x114m72 x114m120 ∧
        x114r1 = (s.mem.readLE (BitVec.toNat (s.regs 2) + 8) 8) ∧ x114r2 = (s.mem.readLE (BitVec.toNat (s.regs 2)) 8) ∧ x114r5 = (s.mem.readLE (BitVec.toNat (s.regs 2) + 24) 8) ∧ x114m64 = (s.mem.readLE (BitVec.toNat (s.regs 2) + 16) 8) ∧ x114m72 = (s.mem.readLE (BitVec.toNat (s.regs 2) + 24) 8) ∧ x114m8 = (s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) ∧ x114m16 = (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8) ∧ x114m24 = (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8) ∧ x114m32 = (s.mem.readLE (BitVec.toNat (s.regs 1)) 8) ∧ x114m120 = (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) ∧
        x1d8r3 < 2 ^ 64 ∧ x1d8r4 < 2 ^ 64 ∧ x1d8r6 < 2 ^ 64 ∧ x1d8r7 < 2 ^ 64 ∧ x1d8r9 < 2 ^ 64 ∧
        x1d8r3 + 2 ^ 64 * x1d8r4 + 2 ^ 128 * x1d8r6 + 2 ^ 192 * x1d8r7 + 2 ^ 256 * x1d8r9 = (2 ^ 256 * (((s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3)) 8) / 2 ^ 64) + ((s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8) / 2 ^ 64) + ((s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) / 2 ^ 64) + ((s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) / 2 ^ 64)) +
        2 ^ 256 * ((s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3)) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8)) +
        2 ^ 320 * ((s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8)) +
        2 ^ 384 * ((s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8)) +
        2 ^ 448 * ((s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) + (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8)) +
        2 ^ 512 * ((s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) * (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8))) / 2 ^ 320 ∧
        R4Regs s S1 ∧ R4Mem s S1.mem ) := by
  refine Fv256.Arm64.SegCompose.seg_trans (g_20_114 s S hpc hs hR hM x20r1 x20r2 x20r3 hL hX0 hX1 hX2) ?_
  intro S1 hpc1 hq1
  unfold P_20_114 at hq1
  obtain ⟨x114r0, x114r1, x114r2, x114r3, x114r4, x114r5, x114r6, x114r7, x114r8, x114r9, x114r10, x114r11, x114r12, x114r13, x114r14, x114r15, x114r16, x114r17, x114r19, x114r20, x114r21, x114r22, x114r23, x114r24, x114r25, x114r26, x114m8, x114m16, x114m24, x114m32, x114m40, x114m48, x114m56, x114m64, x114m72, x114m80, x114m88, x114m96, x114m104, x114m112, x114m120, x114m128, x114m136, x114m144, hL1, h_x114r0, h_x114r1, h_x114r2, h_x114r3, h_x114r4, h_x114r5, h_x114r6, h_x114r7, h_x114r8, h_x114r9, h_x114r10, h_x114r11, h_x114r12, h_x114r13, h_x114r14, h_x114r15, h_x114r16, h_x114r17, h_x114r19, h_x114r20, h_x114r21, h_x114r22, h_x114r23, h_x114r24, h_x114r25, h_x114r26, h_x114m8, h_x114m16, h_x114m24, h_x114m32, h_x114m40, h_x114m48, h_x114m56, h_x114m64, h_x114m72, h_x114m80, h_x114m88, h_x114m96, h_x114m104, h_x114m112, h_x114m120, h_x114m128, h_x114m136, h_x114m144, hR1, hM1⟩ := hq1
  refine Fv256.Arm64.SegCompose.seg_trans (g_114_120 s S1 hpc1 hs hR1 hM1 x114r0 x114r1 x114r2 x114r3 x114r4 x114r5 x114r6 x114r7 x114r8 x114r9 x114r10 x114r11 x114r12 x114r13 x114r14 x114r15 x114r16 x114r17 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r25 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL1) ?_
  intro S2 hpc2 hq2
  unfold P_114_120 at hq2
  obtain ⟨x120r6, x120r9, hL2, h_x120r6, h_x120r9, hR2, hM2⟩ := hq2
  refine Fv256.Arm64.SegCompose.seg_trans (g_120_12c s S2 hpc2 hs hR2 hM2 x114r0 x114r1 x114r2 x114r3 x114r4 x114r5 x120r6 x114r7 0 x120r9 x114r10 x114r11 x114r12 x114r13 x114r14 x114r15 x114r16 x114r17 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r25 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL2) ?_
  intro S3 hpc3 hq3
  unfold P_120_12c at hq3
  obtain ⟨x12cr6, x12cr7, x12cr9, hL3, h_x12cr6, h_x12cr7, h_x12cr9, hR3, hM3⟩ := hq3
  refine Fv256.Arm64.SegCompose.seg_trans (g_12c_138 s S3 hpc3 hs hR3 hM3 x114r0 x114r1 x114r2 x114r3 x114r4 x114r5 x12cr6 x12cr7 0 x12cr9 x114r12 x114r13 x114r14 x114r15 x114r16 x114r17 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r25 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL3) ?_
  intro S4 hpc4 hq4
  unfold P_12c_138 at hq4
  obtain ⟨x138r6, x138r7, x138r9, hL4, h_x138r6, h_x138r7, h_x138r9, hR4, hM4⟩ := hq4
  refine Fv256.Arm64.SegCompose.seg_trans (g_138_148 s S4 hpc4 hs hR4 hM4 x114r0 x114r1 x114r2 x114r3 x114r4 x114r5 x138r6 x138r7 0 x138r9 x114r14 x114r15 x114r16 x114r17 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r25 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL4) ?_
  intro S5 hpc5 hq5
  unfold P_138_148 at hq5
  obtain ⟨x148r6, x148r7, x148r9, x148r10, hL5, h_x148r6, h_x148r7, h_x148r9, h_x148r10, hR5, hM5⟩ := hq5
  refine Fv256.Arm64.SegCompose.seg_trans (g_148_158 s S5 hpc5 hs hR5 hM5 x114r1 x114r2 x114r3 x114r4 x114r5 x148r6 x148r7 0 x148r9 x148r10 x114r14 x114r15 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL5) ?_
  intro S6 hpc6 hq6
  unfold P_148_158 at hq6
  obtain ⟨x158r6, x158r7, x158r9, x158r10, hL6, h_x158r6, h_x158r7, h_x158r9, h_x158r10, hR6, hM6⟩ := hq6
  refine Fv256.Arm64.SegCompose.seg_trans (g_158_16c s S6 hpc6 hs hR6 hM6 x114r1 x114r2 x114r3 x114r4 x114r5 x158r6 x158r7 0 x158r9 x158r10 x114r15 x114r21 x114r22 x114r23 x114r24 x114r26 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL6) ?_
  intro S7 hpc7 hq7
  unfold P_158_16c at hq7
  obtain ⟨x16cr4, x16cr6, x16cr7, x16cr9, x16cr10, hL7, h_x16cr4, h_x16cr6, h_x16cr7, h_x16cr9, h_x16cr10, hR7, hM7⟩ := hq7
  refine Fv256.Arm64.SegCompose.seg_trans (g_16c_18c s S7 hpc7 hs hR7 hM7 x114r1 x114r2 x114r3 x16cr4 x114r5 x16cr6 x16cr7 0 x16cr9 x16cr10 x114r15 x114r24 x114m8 x114m16 x114m24 x114m32 x114m40 x114m48 x114m56 x114m64 x114m72 x114m80 x114m88 x114m96 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL7) ?_
  intro S8 hpc8 hq8
  unfold P_16c_18c at hq8
  obtain ⟨x18cr4, x18cr6, x18cr7, x18cr9, x18cr10, hL8, h_x18cr4, h_x18cr6, h_x18cr7, h_x18cr9, h_x18cr10, hR8, hM8⟩ := hq8
  refine Fv256.Arm64.SegCompose.seg_trans (g_18c_1b8 s S8 hpc8 hs hR8 hM8 x114r1 x114r2 x114r3 x18cr4 x114r5 x18cr6 x18cr7 0 x18cr9 x18cr10 x114r15 x114m8 x114m16 x114m24 x114m32 x114m56 x114m64 x114m72 x114m80 x114m88 x114m104 x114m112 x114m120 x114m128 x114m136 x114m144 hL8) ?_
  intro S9 hpc9 hq9
  unfold P_18c_1b8 at hq9
  obtain ⟨x1b8r4, x1b8r6, x1b8r7, x1b8r9, x1b8r10, hL9, h_x1b8r4, h_x1b8r6, h_x1b8r7, h_x1b8r9, h_x1b8r10, hR9, hM9⟩ := hq9
  refine Fv256.Arm64.SegCompose.seg_mono (g_1b8_1d8 s S9 hpc9 hs hR9 hM9 x114r1 x114r2 x114r3 x1b8r4 x114r5 x1b8r6 x1b8r7 0 x1b8r9 x1b8r10 x114m8 x114m16 x114m24 x114m32 x114m64 x114m72 x114m80 x114m120 x114m128 x114m136 hL9) ?_
  intro S10 hq10
  unfold P_1b8_1d8 at hq10
  obtain ⟨x1d8r3, x1d8r4, x1d8r6, x1d8r7, x1d8r9, hL10, h_x1d8r3, h_x1d8r4, h_x1d8r6, h_x1d8r7, h_x1d8r9, hR10, hM10⟩ := hq10
  have hQ := q_chain (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 32) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 40) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 48) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 56) 8) (s.mem.readLE (BitVec.toNat (s.regs 3)) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8) x114r0 x114r3 x114r4 x114r6 x114r7 x114r8 x114r9 x114r10 x114r11 x114r12 x114r13 x114r14 x114r15 x114r16 x114r17 x114r19 x114r20 x114r21 x114r22 x114r23 x114r24 x114r25 x114r26 x114m40 x114m48 x114m56 x114m80 x114m88 x114m96 x114m104 x114m112 x114m128 x114m136 x114m144 x120r6 x120r9 x12cr6 x12cr7 x12cr9 x138r6 x138r7 x138r9 x148r6 x148r7 x148r9 x148r10 x158r6 x158r7 x158r9 x158r10 x16cr4 x16cr6 x16cr7 x16cr9 x16cr10 x18cr4 x18cr6 x18cr7 x18cr9 x18cr10 x1b8r4 x1b8r6 x1b8r7 x1b8r9 x1b8r10 x1d8r3 x1d8r4 x1d8r6 x1d8r7 x1d8r9
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _) (Fv256.Util.readLE8_lt _ _)
    h_x114r0 h_x114r3 h_x114r4 h_x114r6 h_x114r7 h_x114r8 h_x114r9 h_x114r10 h_x114r11 h_x114r12 h_x114r13 h_x114r14 h_x114r15 h_x114r16 h_x114r17 h_x114r19 h_x114r20 h_x114r21 h_x114r22 h_x114r23 h_x114r24 h_x114r25 h_x114r26 h_x114m40 h_x114m48 h_x114m56 h_x114m80 h_x114m88 h_x114m96 h_x114m104 h_x114m112 h_x114m128 h_x114m136 h_x114m144 h_x120r6 h_x120r9 h_x12cr6 h_x12cr7 h_x12cr9 h_x138r6 h_x138r7 h_x138r9 h_x148r6 h_x148r7 h_x148r9 h_x148r10 h_x158r6 h_x158r7 h_x158r9 h_x158r10 h_x16cr4 h_x16cr6 h_x16cr7 h_x16cr9 h_x16cr10 h_x18cr4 h_x18cr6 h_x18cr7 h_x18cr9 h_x18cr10 h_x1b8r4 h_x1b8r6 h_x1b8r7 h_x1b8r9 h_x1b8r10 h_x1d8r3 h_x1d8r4 h_x1d8r6 h_x1d8r7 h_x1d8r9
  have b_x1d8r3 : x1d8r3 < 2 ^ 64 := by rw [h_x1d8r3]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r4 : x1d8r4 < 2 ^ 64 := by rw [h_x1d8r4]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r6 : x1d8r6 < 2 ^ 64 := by rw [h_x1d8r6]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r7 : x1d8r7 < 2 ^ 64 := by rw [h_x1d8r7]; exact Nat.mod_lt _ (by decide)
  have b_x1d8r9 : x1d8r9 < 2 ^ 64 := by rw [h_x1d8r9]; exact Nat.mod_lt _ (by decide)
  exact ⟨x114r1, x114r2, x114r5, x114m64, x114m72, x114m8, x114m16, x114m24, x114m32, x114m120, x1d8r3, x1d8r4, x1d8r6, x1d8r7, x1d8r9, hL10, h_x114r1, h_x114r2, h_x114r5, h_x114m64, h_x114m72, h_x114m8, h_x114m16, h_x114m24, h_x114m32, h_x114m120, b_x1d8r3, b_x1d8r4, b_x1d8r6, b_x1d8r7, b_x1d8r9, hQ, hR10, hM10⟩

end Fv256.Arm64.R4Seg
