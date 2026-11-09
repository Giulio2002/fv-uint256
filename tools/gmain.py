#!/usr/bin/env python3
import sys; sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
from gb3 import *
b=bnd
A='(s.regs 0).toNat'
out='''import Fv256.Proofs.Amd64.RecipSeg1
import Fv256.Proofs.Amd64.RecipStart
import Fv256.Proofs.Amd64.RecipStage23
import Fv256.Proofs.Amd64.RecipStage4
import Fv256.Proofs.Amd64.RecipStage5
import Fv256.Proofs.Amd64.RecipTail
import Fv256.Proofs.Amd64.RecipEpi
import Fv256.Proofs.Amd64.RecipPaths
import Fv256.Proofs.Amd64.RecipBridge
import Fv256.Proofs.Common.RecipChain
import Fv256.Proofs.Amd64.RecipMainLem

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.F

namespace Fv256.Amd64.RecipSeg

/-- the 32-byte input as four limbs -/
theorem m_limbs (s : State) :
    s.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 0).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 0).toNat + 8) 8 +
      2 ^ 128 * s.mem.readLE ((s.regs 0).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 0).toNat + 24) 8 := Util.readLE_32 _ _

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem main_path (s : State) (hpc : s.rip = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hnp : ¬ ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) s (fun s' =>
      RecPost s s' (recipModel (s.mem.readLE (s.regs 0).toNat 32))) := by
  have hlow : 576 ≤ (s.regs 4).toNat := by have := hpre.2.1; omega
  refine Fv256.SegCompose.seg_trans (seg01 s hpc hpre hm3 hnp) ?_
  intro S1 hpc1 hq1
  obtain ⟨y3, x14crax, x14crcx, x14crdx, x14crbx, x14crsi, x14crdi, x14cr8, x14cr9, x14cm208, x14cm210, x14cm218, x14cm220, hL, hst, hR, hM⟩ := start14c s S1 hlow hq1
  have bY0 := %(b0)s
  have bY1 := %(b1)s
  have bY2 := %(b2)s
  refine Fv256.SegCompose.seg_trans (stage2 (y3 := y3) s S1 hpc1 hpre hR hM x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 hL hst) ?_
  intro S2 hpc2 hq2
  obtain ⟨x160rcx, x1f3rax, x1f3r10, x1f3mb0, hL2, hR2, hM2, hrcx2, hmb, hr2⟩ := hq2
  refine Fv256.SegCompose.seg_trans (stage3 (y3 := y3) s S2 hpc2 hpre hR2 hM2 x1f3rax x160rcx x14crsi x14crdi x14cr8 x14cr9 x1f3r10 x1f3mb0 x14cm208 x14cm210 x14cm218 x14cm220 hL2 hmb) ?_
  intro S3 hpc3 hq3
  obtain ⟨x43crdx, x43crbx, x43cr8, x43cm98, x43cma0, x43cma8, hL3, hR3, hM3, ea0, ea1, ea2, hr3⟩ := hq3
  have hst0 := hst
  obtain ⟨hax, hbx, hdx, hsi, hm220, hdi, h8, h9, hcx, hY, h63, hlt⟩ := hst0
  rw [ea0, ea1, ea2, hsi, hm220] at hL3
  rw [h9, h8, hdi, hsi] at hr3
  refine Fv256.SegCompose.seg_trans (stage4 (y3 := y3) s S3 hpc3 hpre hR3 hM3 x160rcx x43crdx x43crbx x43cr8 x14cm208 x14cm210 x14cm218 hL3) ?_
  intro S4 hpc4 hq4
  obtain ⟨x801rdx, x801rbx, x801rsi, x801r8, x801r9, x801m40, x801m48, x801m50, x801m60, hL4, hr4, c1, c2, c3, c4, hR4, hM4⟩ := hq4
  rw [c1] at hr4
  refine Fv256.SegCompose.seg_trans (stage5 (y3 := y3) s S4 hpc4 hpre hR4 hM4 x160rcx x801rdx x801rbx x801rsi x801r8 x801r9 x801m40 x801m48 x801m50 x801m60 x14cm208 x14cm210 x14cm218 hL4 c1 c2 c3 c4) ?_
  intro S5 hpc5 hq5
  obtain ⟨xc49rcx, xc49rdx, xc49rbx, xc49rsi, xc49r9, xc49r11, xc49m78, xc49m80, xc49m88, xc49m90, hL5, hrc5, hV5, f1, f2, f3, f4, hR5, hM5⟩ := hq5
  have hcl : Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 :=
    Fv256.Amd64.LshNorm.clz_le _ (Util.readLE8_lt _ _) hm3
  have hc : xc49rcx < 64 := rcx_lt _ x14crcx x160rcx xc49rcx hcl hcx hrcx2 hrc5
  refine Fv256.SegCompose.seg_trans (g_tail (y3 := y3) s S5 hpc5 hpre hR5 hM5 xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 hL5 hc f1 f2 f3 f4) ?_
  intro S6 hpc6 hq6
  obtain ⟨d0, d1, d2, d3, d4, hLd, hsum, hR6, hM6⟩ := hq6
  have hsp4 : (S6.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hR6.1]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine Fv256.SegCompose.seg_mono (epi_d1b (y3 := y3) s S6 hpc6 hpre hR6 hM6 hsp4) ?_
  intro S' hS'
  obtain ⟨e4, e5, e14, e15, emem⟩ := hS'
  refine ⟨e4, e5, e14, e15, ?_, ?_⟩
  · -- the result
    rw [emem, readLE_40]
    obtain ⟨hd0, bd0, hd1, bd1, hd2, bd2, hd3, bd3, hd4, bd4⟩ := hLd
    have a1 : (s.regs 4).toNat + 8 + 8 = (s.regs 4).toNat + 16 := by omega
    have a2 : (s.regs 4).toNat + 8 + 16 = (s.regs 4).toNat + 24 := by omega
    have a3 : (s.regs 4).toNat + 8 + 24 = (s.regs 4).toNat + 32 := by omega
    have a4 : (s.regs 4).toNat + 8 + 32 = (s.regs 4).toNat + 40 := by omega
    rw [a1, a2, a3, a4, hd0, hd1, hd2, hd3, hd4, hsum]
    -- bridge to the model
    have hmod : recipModel (s.mem.readLE (s.regs 0).toNat 32) = recipTail (recipS (s.mem.readLE (s.regs 0).toNat 32)) (recipR4 (recipY (s.mem.readLE (s.regs 0).toNat 32))) := by
      have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
      have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
      have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
      have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
      have hm192 : ¬ (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192) := by
        rw [m_limbs s]
        have : 0 < s.mem.readLE ((s.regs 0).toNat + 24) 8 := Nat.pos_of_ne_zero hm3
        omega
      have hpw : ¬ (s.mem.readLE (s.regs 0).toNat 32 = 2 ^ Nat.log2 (s.mem.readLE (s.regs 0).toNat 32)) := by
        intro h
        apply hnp
        rw [m_limbs s] at h
        exact (pow2_test _ _ _ _ bb0 bb1 bb2 bb3 hm3).2 h
      unfold recipModel
      rw [if_neg hm192, if_neg hpw]
    rw [hmod, m_limbs s]
    exact chain_final _ _ _ _ x14cm208 x14cm210 x14cm218 y3 (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) hm3
      bY0 bY1 bY2 hlt h63 (by rw [← m_limbs s]; exact hY) x14crax x14crbx x14crdx hax hbx hdx x1f3rax x1f3r10 hr2 x43crbx x43cr8 x43crdx hr3
      x801m60 x801rbx x801m50 x801m48 x801m40 hr4 x160rcx x14crcx xc49rcx (xc49rdx + 2 ^ 64 * xc49rbx + 2 ^ 128 * xc49rsi + 2 ^ 192 * xc49r9 + 2 ^ 256 * xc49r11) hrcx2 hcx hrc5 _ rfl hV5
  · rw [emem]; exact hM6.2.2.2

end Fv256.Amd64.RecipSeg
''' % dict(b0=b('L14c','x14cm208','hL'),b1=b('L14c','x14cm210','hL'),b2=b('L14c','x14cm218','hL'))
open('/srv/fv-uint256-wBm/lean/Fv256/Proofs/Amd64/RecipMain.lean','w').write(out)
