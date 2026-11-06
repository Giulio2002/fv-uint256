import Fv256.Amd64.RecipArith5p
import Fv256.Amd64.RecipArith5q
import Fv256.Amd64.RecipArith5c
import Fv256.Amd64.RecipArith5d
import Fv256.Amd64.RecipStage5Lem
import Fv256.Amd64.RecipG.C_801_9d4
import Fv256.Amd64.RecipG.C_9d4_b47
import Fv256.Amd64.RecipG.G_b47_b9f
import Fv256.Amd64.RecipG.G_b9f_bed
import Fv256.Amd64.RecipG.G_bed_c49

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage5 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x801)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 : Nat)
    (hL : L801 s S x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 y3)
    (e1 : x801rdx = x801m60) (e2 : x801r8 = x801m50) (e3 : x801r9 = x801m48) (e4 : x801rsi = x801m40) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xc49)) S (fun S' =>
      ∃ xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90,
        Lc49 s S' xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 ∧
        xc49rcx = (if 2 ^ 63 ≤ x801rcx then 0 else x801rcx) ∧
        xc49rdx + 2 ^ 64 * xc49rbx + 2 ^ 128 * xc49rsi + 2 ^ 192 * xc49r9 + 2 ^ 256 * xc49r11 =
          (if 2 ^ 63 ≤ x801rcx then 2 * (if 2 ^ 574 < (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) * (x801m208 + 2 ^ 64 * x801m210 + 2 ^ 128 * x801m218 + 2 ^ 192 * y3) then ((x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) + 2 ^ 320 - 1) % 2 ^ 320 else (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40)) % 2 ^ 320 else (if 2 ^ 574 < (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) * (x801m208 + 2 ^ 64 * x801m210 + 2 ^ 128 * x801m218 + 2 ^ 192 * y3) then ((x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) + 2 ^ 320 - 1) % 2 ^ 320 else (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40))) ∧
        xc49m78 = xc49rbx ∧ xc49m80 = xc49rsi ∧ xc49m88 = xc49r9 ∧ xc49m90 = xc49r11 ∧
        RecRegs s S' ∧ RecMem s S'.mem y3) := by
  refine Fv256.SegCompose.seg_trans (c_801_9d4 (y3 := y3) s S hpc hs hR hM x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 y3 hL) ?_
  intro S1 hpc1 hq1
  have hP := sum5p s y3 x801rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x801m208 x801m210 x801m218 y3 S1 hq1 (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) e1 e2 e3 e4
  obtain ⟨x9d4rax, x9d4rdx, x886r10, x92dr11, x886r12, x886r13, x886r15, x886m68, x886m70, x9d4mc0, x92dmc8, x92dmd0, x886md8, x886me0, x886m100, x9d4m160, x9d4m168, x9d4m170, x9d4m178, x9d4m180, x9d4m188, x9d4m190, x9d4m198, x9d4m1a0, x92dm1a8, x92dm1b0, x92dm1b8, x92dm1c0, x92dm1c8, x92dm1d0, x92dm1d8, x92dm1e0, x92dm1e8, x92dm1f0, x886m1f8, x886m200, x886m208, x92dm210, x9d4m218, x9d4m220, hL1, hR1, hM1, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19⟩ := hP
  refine Fv256.SegCompose.seg_trans (c_9d4_b47 (y3 := y3) s S1 hpc1 hs hR1 hM1 x9d4rax x801rcx x9d4rdx x801rbx x886r10 x92dr11 x886r12 x886r13 x886r15 x801m40 x801m48 x801m50 x801m60 x886m68 x886m70 x9d4mc0 x92dmc8 x92dmd0 x886md8 x886me0 x886m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x886m1f8 x886m200 x886m208 x92dm210 x9d4m218 x9d4m220 hL1) ?_
  intro S2 hpc2 hq2
  have hlh00 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f0
  have hlh01 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f1
  have hlh02 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f2
  have hlh03 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f3
  have hlh10 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f4
  have hlh11 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f5
  have hlh12 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f6
  have hlh13 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f7
  have hlh20 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f8
  have hlh21 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f9
  have hlh22 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f10
  have hlh23 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f11
  have hlh30 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f12
  have hlh31 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.1) f13
  have hlh32 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f14
  have hlh33 := lohi _ _ _ (hL1.2.1) f15
  have hlh40 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f16
  have hlh41 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f17
  have hlh42 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f18
  have hlh43 := lohi _ _ _ (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f19
  have hQ := sum5q s y3 x9d4rax x801rcx x9d4rdx x801rbx x886r10 x92dr11 x886r12 x886r13 x886r15 x801m40 x801m48 x801m50 x801m60 x886m68 x886m70 x9d4mc0 x92dmc8 x92dmd0 x886md8 x886me0 x886m100 x9d4m160 x9d4m168 x9d4m170 x9d4m178 x9d4m180 x9d4m188 x9d4m190 x9d4m198 x9d4m1a0 x92dm1a8 x92dm1b0 x92dm1b8 x92dm1c0 x92dm1c8 x92dm1d0 x92dm1d8 x92dm1e0 x92dm1e8 x92dm1f0 x886m1f8 x886m200 x886m208 x92dm210 x9d4m218 x9d4m220 x801m60 x801rbx x801m50 x801m48 x801m40 x801m208 x801m210 x801m218 y3 S2 hq2 (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hlh00.1 hlh00.2 hlh01.1 hlh01.2 hlh02.1 hlh02.2 hlh03.1 hlh03.2 hlh10.1 hlh10.2 hlh11.1 hlh11.2 hlh12.1 hlh12.2 hlh13.1 hlh13.2 hlh20.1 hlh20.2 hlh21.1 hlh21.2 hlh22.1 hlh22.2 hlh23.1 hlh23.2 hlh30.1 hlh30.2 hlh31.1 hlh31.2 hlh32.1 hlh32.2 hlh33.1 hlh33.2 hlh40.1 hlh40.2 hlh41.1 hlh41.2 hlh42.1 hlh42.2 hlh43.1 hlh43.2
  obtain ⟨xb47rax, xb47rdx, xa49rsi, xb47r8, xb27r10, xab4r12, xb47r13, xb47r15, hL2, hR2, hM2, hT⟩ := hQ
  refine Fv256.SegCompose.seg_trans (g_b47_b9f (y3 := y3) s S2 hpc2 hs hR2 hM2 xb47rax x801rcx xb47rdx x801rbx xa49rsi xb47r8 xb27r10 xab4r12 xb47r13 xb47r15 x801m40 x801m48 x801m50 x801m60 x886m100 hL2) ?_
  intro S3 hpc3 hq3
  obtain ⟨xb9frdx, hL3, hc, hR3, hM3⟩ := hq3
  have hc2 := sum5c x886m100 xa49rsi xab4r12 xb27r10 xb47r8 xb47r15 xb47rax xb47rdx xb47r13 xb9frdx (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (hL2.2.2.2.2.2.2.2.2.2.1) (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL2.2.2.2.2.2.2.2.2.2.2.2.1) (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL2.2.1) (hL2.2.2.2.2.2.1) (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hc
  refine Fv256.SegCompose.seg_trans (g_b9f_bed (y3 := y3) s S3 hpc3 hs hR3 hM3 x801rcx xb9frdx x801rbx x801m40 x801m48 x801m50 x801m60 hL3) ?_
  intro S4 hpc4 hq4
  obtain ⟨xbedrdi, xbedr8, xbedr10, xbedr12, xbedr15, hL4, hdi, hd8, hd10, hd12, hd15, hR4, hM4⟩ := hq4
  have hd := sum5d xb9frdx x801m60 x801rbx x801m50 x801m48 x801m40 xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 (by rw [hc2]; split <;> omega) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2) (hL3.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.1) hdi hd8 hd10 hd12 hd15
  refine Fv256.SegCompose.seg_mono (g_bed_c49 (y3 := y3) s S4 hpc4 hs hR4 hM4 x801rcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 hL4) ?_
  intro S5 hq5
  unfold P_bed_c49 at hq5
  obtain ⟨xc49rcx, xc49rdx, xc49rbx, xc49rsi, xc49r9, xc49r11, xc49m78, xc49m80, xc49m88, xc49m90, hL5, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, hR5, hM5⟩ := hq5
  have hW : xbedrdi + 2 ^ 64 * xbedr8 + 2 ^ 128 * xbedr10 + 2 ^ 192 * xbedr12 + 2 ^ 256 * xbedr15 = (if 2 ^ 574 < (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) * (x801m208 + 2 ^ 64 * x801m210 + 2 ^ 128 * x801m218 + 2 ^ 192 * y3) then ((x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40) + 2 ^ 320 - 1) % 2 ^ 320 else (x801m60 + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40)) := by
    rw [hT, stage5T_eq] at hc2
    refine r4step _ _ _ _ _ (by omega) ?_ hc2 rfl
    rcases hd with h | ⟨h0, h1, h2, h3, h4, hcc, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hcc, hw⟩
  have bd0 := (hL4.2.2.2.1)
  have bd1 := (hL4.2.2.2.2.2.1)
  have bd2 := (hL4.2.2.2.2.2.2.2.1)
  have bd3 := (hL4.2.2.2.2.2.2.2.2.2.1)
  have bd4 := (hL4.2.2.2.2.2.2.2.2.2.2.2)
  have bcx := (hL.2.1)
  have hdb := dbl5 x801rcx xbedrdi xbedr8 xbedr10 xbedr12 xbedr15 xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 bcx bd0 bd1 bd2 bd3 bd4 g1 g2 g3 g4 g5
  rw [hW] at hdb
  refine ⟨xc49rcx, xc49rdx, xc49rbx, xc49rsi, xc49r9, xc49r11, xc49m78, xc49m80, xc49m88, xc49m90, hL5, rcx_dbl _ _ bcx g0, hdb, ?_, ?_, ?_, ?_, hR5, hM5⟩
  · exact cpy _ _ _ _ _ bd1 g2 g6
  · exact cpy _ _ _ _ _ bd2 g3 g7
  · exact cpy _ _ _ _ _ bd3 g4 g8
  · exact cpy _ _ _ _ _ bd4 g5 g9

end Fv256.Amd64.RecipSeg
