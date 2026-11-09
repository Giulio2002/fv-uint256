import Fv256.Proofs.Amd64.RecipArith4
import Fv256.Proofs.Amd64.RecipArith4p
import Fv256.Proofs.Amd64.RecipArith4q
import Fv256.Proofs.Amd64.RecipArith4s
import Fv256.Proofs.Amd64.RecipStage5Lem
import Fv256.Proofs.Amd64.RecipG.C_43c_502
import Fv256.Proofs.Amd64.RecipG.C_502_660
import Fv256.Proofs.Amd64.RecipG.C_660_7ae
import Fv256.Proofs.Amd64.RecipG.G_7ae_801

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

/-- the seven-word sum of stage 4 in terms of the squaring words `w_i` and `y_j` -/
def stage4T (w0 w1 w2 w3 w4 w5 y0 y1 y2 y3 : Nat) : Nat :=
  2 ^ 0 * (w0 * y3 + w1 * y2 + w2 * y1 + w3 * y0) + 2 ^ 64 * (w1 * y3 + w2 * y2 + w3 * y1 + w4 * y0) + 2 ^ 128 * (w2 * y3 + w3 * y2 + w4 * y1 + w5 * y0) + 2 ^ 192 * (w3 * y3 + w4 * y2 + w5 * y1) + 2 ^ 256 * (w4 * y3 + w5 * y2) + 2 ^ 320 * (w5 * y3)

/-- the machine value of `r4pre` (`recipR4pre`) from `r3` and the words of `y` -/
def r4preF (r3 y0 y1 y2 y3 : Nat) : Nat :=
  (r3 * 2 ^ 256 + 2 ^ 448 - stage4T (sqw r3 0) (sqw r3 1) (sqw r3 2) (sqw r3 3) (sqw r3 4) (sqw r3 5) y0 y1 y2 y3) % 2 ^ 448 / 2 ^ 128

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage4 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x43c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x43crcx x43crdx x43crbx x43cr8 x43cm208 x43cm210 x43cm218 : Nat)
    (hL : L43c s S x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x801)) S (fun S' =>
      ∃ x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60,
        L801 s S' x43crcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x43cm208 x43cm210 x43cm218 y3 ∧
        x801rdx + 2 ^ 64 * x801rbx + 2 ^ 128 * x801m50 + 2 ^ 192 * x801m48 + 2 ^ 256 * x801m40 =
          r4preF (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) x43cm208 x43cm210 x43cm218 y3 ∧
        x801rdx = x801m60 ∧ x801r8 = x801m50 ∧ x801r9 = x801m48 ∧ x801rsi = x801m40 ∧
        RecRegs s S' ∧ RecMem s S'.mem y3) := by
  refine Fv256.SegCompose.seg_trans (c_43c_502 (y3 := y3) s S hpc hs hR hM x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL) ?_
  intro S1 hpc1 hq1
  have hA := sum4a s y3 x43crcx x43crdx x43crbx y3 x43cr8 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 S1 hq1 (hL.2.2.2.1) (hL.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.1)
  obtain ⟨x502rbx, x502rdi, x502r8, x502r9, x502r10, x502m68, x502m70, hL1, hR1, hM1, e1, e2, e3, e4, e5, e0⟩ := hA
  refine Fv256.SegCompose.seg_trans (c_502_660 (y3 := y3) s S1 hpc1 hs hR1 hM1 x43crcx x502rbx y3 x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL1) ?_
  intro S2 hpc2 hq2
  have hP := sum4p s y3 x43crcx x502rbx y3 x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 S2 hq2 (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) rfl
  obtain ⟨x660rax, x660rdi, x660r8, x660r9, x660r10, x549r15, x5e2m38, x5e2m40, x549m48, x549m50, x549m58, x660m150, x660m158, x660m160, x660m168, x660m170, x660m178, x660m180, x660m188, x660m190, x5e2m198, x5e2m1a0, x5e2m1a8, x5e2m1b0, x5e2m1b8, x5e2m1c0, x5e2m1c8, x5e2m1d0, x5e2m1d8, x5e2m1e0, x5e2m1e8, x5e2m1f0, x549m1f8, x549m200, hL2, hR2, hM2, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := hP
  refine Fv256.SegCompose.seg_trans (c_660_7ae (y3 := y3) s S2 hpc2 hs hR2 hM2 x660rax x43crcx x660rdi x660r8 x660r9 x660r10 x549r15 x5e2m38 x5e2m40 x549m48 x549m50 x549m58 x502m68 x502m70 x43cr8 x43crbx x43crdx x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x549m1f8 x549m200 x43cm208 x43cm210 x43cm218 y3 hL2) ?_
  intro S3 hpc3 hq3
  have hlh12 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f3
  have hlh13 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f9
  have hlh21 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f4
  have hlh22 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f15
  have hlh23 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f10
  have hlh30 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f0
  have hlh31 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f16
  have hlh32 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f5
  have hlh33 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f11
  have hlh40 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f1
  have hlh41 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f6
  have hlh42 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f14
  have hlh43 := lohi _ _ _ (hL2.2.1) f12
  have hlh50 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f2
  have hlh51 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f7
  have hlh52 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f8
  have hlh53 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) f13
  have hlh03 := lohi _ _ _ (hL2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) e0
  have hQ := sum4q s y3 x660rax x43crcx x660rdi x660r8 x660r9 x660r10 x549r15 x5e2m38 x5e2m40 x549m48 x549m50 x549m58 x502m68 x502m70 x43cr8 x43crbx x43crdx x660m150 x660m158 x660m160 x660m168 x660m170 x660m178 x660m180 x660m188 x660m190 x5e2m198 x5e2m1a0 x5e2m1a8 x5e2m1b0 x5e2m1b8 x5e2m1c0 x5e2m1c8 x5e2m1d0 x5e2m1d8 x5e2m1e0 x5e2m1e8 x5e2m1f0 x549m1f8 x549m200 x43cm208 x43cm210 x43cm218 y3  (sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 0) x502r10 x502rdi x502r8 x502rbx x502r9 x43cm208 x43cm210 x43cm218 y3 S3 hq3 (Nat.mod_lt _ (by decide)) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hlh12.1 hlh12.2 hlh13.1 hlh13.2 hlh21.1 hlh21.2 hlh22.1 hlh22.2 hlh23.1 hlh23.2 hlh30.1 hlh30.2 hlh31.1 hlh31.2 hlh32.1 hlh32.2 hlh33.1 hlh33.2 hlh40.1 hlh40.2 hlh41.1 hlh41.2 hlh42.1 hlh42.2 hlh43.1 hlh43.2 hlh50.1 hlh50.2 hlh51.1 hlh51.2 hlh52.1 hlh52.2 hlh53.1 hlh53.2 hlh03.1 hlh03.2
  obtain ⟨x7aerax, x7aerdx, x7aerbx, x7aersi, x7aerdi, x7aer8, x7aer11, hL3, hR3, hM3, hT⟩ := hQ
  refine Fv256.SegCompose.seg_mono (g_7ae_801 (y3 := y3) s S3 hpc3 hs hR3 hM3 x7aerax x43crcx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x43cr8 x43crbx x43crdx x43cm208 x43cm210 x43cm218 y3 hL3) ?_
  intro S4 hq4
  unfold P_7ae_801 at hq4
  obtain ⟨x801rdx, x801rbx, x801rsi, x801r8, x801r9, x801m40, x801m48, x801m50, x801m60, hL4, h_x801rdx, h_x801rbx, h_x801rsi, h_x801r8, h_x801r9, h_x801m40, h_x801m48, h_x801m50, h_x801m60, hR4, hM4⟩ := hq4
  have hsb := sbb4 x7aerax x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x43cr8 x43crbx x43crdx x801rdx x801rbx x801m50 x801m48 x801m40 (hL3.2.1) (hL3.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) h_x801rdx h_x801rbx h_x801m40 h_x801m48 h_x801m50
  refine ⟨x801rdx, x801rbx, x801rsi, x801r8, x801r9, x801m40, x801m48, x801m50, x801m60, hL4, ?_, h_x801rdx.trans h_x801m60.symm, h_x801r8.trans h_x801m50.symm, h_x801r9.trans h_x801m48.symm, h_x801rsi.trans h_x801m40.symm, hR4, hM4⟩
  rw [hsb, hT]
  subst e1 e2 e3 e4 e5
  rfl

end Fv256.Amd64.RecipSeg
