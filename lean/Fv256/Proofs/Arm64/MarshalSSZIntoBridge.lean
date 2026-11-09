import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Common.SszBridge
import Fv256.Spec.MarshalSSZInto
import Fv256.Proofs.Arm64.MarshalSSZIntoMain

/-!
# arm64: `MarshalSSZInto` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZInto.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : Janus.Contracts.RtInv) (Ri : Janus.Spec.Type.IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) :
    (Fv256.Arm64.MarshalSSZIntoMain.Post R Ri L bud e tp tl z dp len cap s s') ↔
    ((32 ≤ len.toNat →
      s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 1 = len - 32#64 ∧
      s'.regs 2 = cap - 32#64 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
      (List.range 32).map (fun i => s'.mem.readLE (dp.toNat + i) 1) = Fv256.Spec.marshalSSZInto (val256 s.mem z.toNat) ∧
      MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) ∧
    (len.toNat < 32 → Fv256.Arm64.MarshalSSZIntoMain.ErrPost R Ri L bud e tp tl z dp len cap s s')) := by
  unfold Fv256.Arm64.MarshalSSZIntoMain.Post Fv256.Arm64.MarshalSSZIntoMain.SuccPost
  simp only [Janus.Spec.val256, ← Fv256.Proofs.Bytes.mem_leBytes_iff_rd]
  try exact Iff.rfl

end Fv256.Arm64.MarshalSSZInto.Bridge
