import Fv256.Amd64.RecipArith2
import Fv256.Amd64.RecipArith3
import Fv256.Amd64.RecipStart
import Fv256.Amd64.RecipG.C_14c_1f3
import Fv256.Amd64.RecipG.C_1f3_43c

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage2 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x14c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat)
    (hL : L14c s S x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) (hst : Start14c s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1f3)) S (fun S' =>
      ∃ x160rcx x1f3rax x1f3r10 x1f3mb0, L1f3 s S' x1f3rax x160rcx x14crsi x14crdi x14cr8 x14cr9 x1f3r10 x1f3mb0 x14cm208 x14cm210 x14cm218 x14cm220 ∧ RecRegs s S' ∧ RecMem s S'.mem y3 ∧
      x160rcx = (x14crcx % 64 + 18446744073709551615) % 18446744073709551616 ∧ x1f3mb0 = x1f3rax ∧
      x1f3rax + 18446744073709551616 * x1f3r10 = (if ((2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128 = 0 ∧ x14crbx = 0) then 2 ^ 128 - 1 else (2 * (r1c x14crax x14crdx * 18446744073709551616) + 2 ^ 128 - (2 * stage2e (r1c x14crax x14crdx) x14cm218 y3) % 2 ^ 128) % 2 ^ 128)) := by
  refine Fv256.SegCompose.seg_mono (c_14c_1f3 (y3 := y3) s S hpc hs hR hM x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 hL) ?_
  intro S1 hq1
  exact sum2 s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 S1 hq1 hst (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem stage3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x1f3)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 : Nat)
    (hL : L1f3 s S x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220) (hmb : x1f3mb0 = x1f3rax) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x43c)) S (fun S' =>
      ∃ x43crdx x43crbx x43cr8 x43cm98 x43cma0 x43cma8, L43c s S' x1f3rcx x43crdx x43crbx x1f3rsi x43cr8 x43cm98 x43cma0 x43cma8 x1f3m208 x1f3m210 x1f3m218 x1f3m220 ∧ RecRegs s S' ∧ RecMem s S'.mem y3 ∧
      x43cma0 = x43crbx ∧ x43cm98 = x43cr8 ∧ x43cma8 = x43crdx ∧
      x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx =
        2 * ((((x1f3rax + 2 ^ 64 * x1f3r10) * 2 ^ 192 + 2 ^ 320 - (stage3q (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 0) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 1) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 2) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 3) x1f3r9 x1f3r8 x1f3rdi x1f3rsi)) % 2 ^ 320) / 2 ^ 128) % 2 ^ 192) := by
  refine Fv256.SegCompose.seg_mono (c_1f3_43c (y3 := y3) s S hpc hs hR hM x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 hL) ?_
  intro S1 hq1
  exact sum3 s y3 x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 S1 hq1 (hL.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.1) (hL.2.2.2.2.2.2.2.2.2.2.2.1) hmb

end Fv256.Amd64.RecipSeg
