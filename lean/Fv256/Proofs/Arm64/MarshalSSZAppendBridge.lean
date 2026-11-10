import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.MarshalSSZAppend
import Fv256.Proofs.Arm64.MarshalSSZAppendMain

/-!
# arm64: `MarshalSSZAppend` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa Fv256.Arm64.MarshalSSZAppendG
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZAppend.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (s s' : State) :
    (AppendPost R s s' z dp.toNat len.toNat cap.toNat b L) ↔
    ((s'.regs 1).toNat = len.toNat + 32 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ len.toNat + 32 ≤ (s'.regs 2).toNat ∧
    (List.range 32).map (fun i => s'.mem.readLE ((s'.regs 0).toNat + len.toNat + i) 1) = Fv256.Spec.marshalSSZAppend (val256 s.mem z.toNat) ∧
    (∀ i, i < len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp.toNat + i)) ∧
    (len.toNat + 32 ≤ cap.toNat → (s'.regs 0).toNat = dp.toNat ∧ (s'.regs 2).toNat = cap.toNat ∧
      R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
      MemFrame s.mem s'.mem [(dp.toNat + len.toNat, dp.toNat + len.toNat + 32), (s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
    (cap.toNat < len.toNat + 32 → InRanges (s'.regs 0).toNat (s'.regs 2).toNat R.rt ∧
      (∃ b' L', R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ InRanges (s'.regs 0).toNat (s'.regs 2).toNat L') ∧
      MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp.toNat, dp.toNat + cap.toNat)]))) := by
  unfold Fv256.Arm64.MarshalSSZAppendG.AppendPost
  simp only [Janus.Spec.val256, ← Fv256.Proofs.Bytes.mem_leBytes_iff_rd]
  try exact Iff.rfl

end Fv256.Arm64.MarshalSSZAppend.Bridge
