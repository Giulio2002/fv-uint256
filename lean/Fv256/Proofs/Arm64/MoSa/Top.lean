import Fv256.Proofs.Arm64.MulOverflowProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilSa
import Fv256.Proofs.Arm64.MoSa.A
import Fv256.Proofs.Arm64.MoSa.B
import Fv256.Proofs.Arm64.MoSa.C
import Fv256.Proofs.Arm64.MoSa.D
import Fv256.Proofs.Arm64.MoSa.E

/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (arm64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`X0` receiver, `X1`, `X2`) with the 32 bytes at `z` writable and those at `x`, `y` readable
(below `2^48`), every pair of the three pointers equal or disjoint, the 256-byte window below the stack pointer (`StackOK s 240 16`: the
function's frame and the extracted `umul` callee's) disjoint from the three objects, and a Go call whose stack check falls through
(`GuardOK s 0`): the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the overflow flag in `X1` is `1` iff
`x*y >= 2^256`, the number at `z` afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside
`z[0..32)` and the stack window. One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with flag `0` and value `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MoSa

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Fv256.Arm64.MulOverflowProg.program Fv256.Arm64.MulOverflowProg.entry [z, x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
        Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 240) 256)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        UtilSa.OnlyWrites3 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 232 (s.sp.toNat + 8) 8) := by
  intro ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩


/-- the library summary of `(*Int).MulOverflow` (over the Extracted-free program `MulOverflowProg.program`) -/
theorem mo_summary (z x y : BitVec 64) :
    Janus.Tactic.Summary Fv256.Arm64.MulOverflowProg.program Fv256.Arm64.MulOverflowProg.entry
      (fun s => ∃ ret, RetAddr Fv256.Arm64.MulOverflowProg.program ret ∧
        CallSetup (Fv256.Arm64.MulOverflowProg.program.withExit ret) Fv256.Arm64.MulOverflowProg.entry [z, x, y] s ∧
        (GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
        Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 240) 256))
      (fun s s' => ABIReturn s s' ∧ (s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        UtilSa.OnlyWrites3 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 232 (s.sp.toNat + 8) 8)) :=
  Ensures.toSummary (correctness z x y) (by decide)

end Fv256.Arm64.MoSa
