import Fv256.Amd64.RecipG.G_14c_160
import Fv256.Amd64.RecipG.G_160_1c1
import Fv256.Amd64.RecipG.G_1c1_1d0
import Fv256.Amd64.RecipG.G_1d0_1f3

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def PC_14c_1f3 (s : State) (y3 : Nat) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat) (S' : State) : Prop :=
  ∃ x160rax x160rcx x1c1rax x1c1rdx x1c1r10 x1d0r10 x1d0r11 x1f3rax x1f3r10 x1f3mb0, L1f3 s S' x1f3rax x160rcx x14crsi x14crdi x14cr8 x14cr9 x1f3r10 x1f3mb0 x14cm208 x14cm210 x14cm218 x14cm220 ∧ x160rax = (if x14crdx = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x14crax).toNat ∧ x160rcx = (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x14crcx) &&& 63#32) - 1#64).toNat ∧ x1c1rax = ((x14crsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x14crsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x14crsi % 18446744073709551616 + x14crdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x14crdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x14crsi % 18446744073709551616 + x14crdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x14crdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1c1rdx = (x14crsi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + (x14crsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x14crsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x14crsi % 18446744073709551616 + x14crdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 + ((x14crsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x14crsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x14crsi % 18446744073709551616 + x14crdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x14crdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x14crsi % 18446744073709551616 + x14crdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x14crdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1c1r10 = x160rax % 18446744073709551616 ∧ x1d0r10 = ((x1c1r10 % 18446744073709551616 + 18446744073709551616 - x1c1rdx % 18446744073709551616 - (decide (0 < x1c1rax)).toNat) % 18446744073709551616 + (x1c1r10 % 18446744073709551616 + 18446744073709551616 - x1c1rdx % 18446744073709551616 - (decide (0 < x1c1rax)).toNat) % 18446744073709551616 + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1d0r11 = ((18446744073709551616 - x1c1rax % 18446744073709551616) % 18446744073709551616 + (18446744073709551616 - x1c1rax % 18446744073709551616) % 18446744073709551616) % 18446744073709551616 ∧ x1f3rax = (if (BitVec.ofNat 64 x14crbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat ∧ x1f3r10 = (if (BitVec.ofNat 64 x14crbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r10).toNat ∧ x1f3mb0 = ((if (BitVec.ofNat 64 x14crbx ||| (BitVec.ofNat 64 x1d0r11 ||| BitVec.ofNat 64 x1d0r10)).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x1d0r11).toNat) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem c_14c_1f3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x14c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat) (hL : L14c s S x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1f3)) S (PC_14c_1f3 s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) := by
  refine Fv256.SegCompose.seg_trans (g_14c_160 (y3 := y3) s S hpc hs hR hM x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 hL) ?_
  intro S1 hpc1 hq1
  unfold P_14c_160 at hq1
  obtain ⟨x160rax, x160rcx, hL1, h_x160rax, h_x160rcx, hR1, hM1⟩ := hq1
  refine Fv256.SegCompose.seg_trans (g_160_1c1 (y3 := y3) s S1 hpc1 hs hR1 hM1 x160rax x160rcx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 hL1) ?_
  intro S2 hpc2 hq2
  unfold P_160_1c1 at hq2
  obtain ⟨x1c1rax, x1c1rdx, x1c1r10, hL2, h_x1c1rax, h_x1c1rdx, h_x1c1r10, hR2, hM2⟩ := hq2
  refine Fv256.SegCompose.seg_trans (g_1c1_1d0 (y3 := y3) s S2 hpc2 hs hR2 hM2 x1c1rax x160rcx x1c1rdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x1c1r10 x14cm208 x14cm210 x14cm218 x14cm220 hL2) ?_
  intro S3 hpc3 hq3
  unfold P_1c1_1d0 at hq3
  obtain ⟨x1d0r10, x1d0r11, hL3, h_x1d0r10, h_x1d0r11, hR3, hM3⟩ := hq3
  refine Fv256.SegCompose.seg_mono (g_1d0_1f3 (y3 := y3) s S3 hpc3 hs hR3 hM3 x160rcx x14crbx x14crsi x14crdi x14cr8 x14cr9 x1d0r10 x1d0r11 x14cm208 x14cm210 x14cm218 x14cm220 hL3) ?_
  intro S4 hq4
  unfold P_1d0_1f3 at hq4
  obtain ⟨x1f3rax, x1f3r10, x1f3mb0, hL4, h_x1f3rax, h_x1f3r10, h_x1f3mb0, hR4, hM4⟩ := hq4
  unfold PC_14c_1f3
  exact ⟨x160rax, x160rcx, x1c1rax, x1c1rdx, x1c1r10, x1d0r10, x1d0r11, x1f3rax, x1f3r10, x1f3mb0, hL4, h_x160rax, h_x160rcx, h_x1c1rax, h_x1c1rdx, h_x1c1r10, h_x1d0r10, h_x1d0r11, h_x1f3rax, h_x1f3r10, h_x1f3mb0, hR4, hM4⟩

end Fv256.Amd64.RecipSeg
