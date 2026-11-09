import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Common.SszBridge
import Fv256.Spec.MarshalSSZInto
import Fv256.Proofs.Amd64.MarshalSSZIntoMain

/-!
# amd64: `MarshalSSZInto` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf
  Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.PoolAmd64
  Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Fv256.Amd64.MarshalSSZInto.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) :
    (Fv256.Amd64.MarshalSSZIntoMain.Post R Ri L bud e tp tl z dp len cap s s') ↔
    ((32 ≤ len.toNat →
      s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 3 = len - 32#64 ∧
      s'.regs 1 = cap - 32#64 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
      (List.range 32).map (fun i => s'.mem.readLE (dp.toNat + i) 1) = Fv256.Spec.marshalSSZInto (valueAt s z 32) ∧
      Janus.MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
        ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]) ∧
    (len.toNat < 32 → Fv256.Amd64.MarshalSSZIntoMain.ErrPost R Ri L bud e tp tl z dp len cap s s')) := by
  unfold Fv256.Amd64.MarshalSSZIntoMain.Post Fv256.Amd64.MarshalSSZIntoMain.SuccPost
  simp only [valueAt, ← Fv256.Proofs.Bytes.mem_leBytes_iff_rd]
  try exact Iff.rfl

end Fv256.Amd64.MarshalSSZInto.Bridge
