import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Common.SszBridge
import Fv256.Spec.UnmarshalSSZ
import Fv256.Proofs.Arm64.UnmarshalSSZMain

/-!
# arm64: `UnmarshalSSZ` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.UnmarshalSSZ.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) :
    (Fv256.Arm64.UnmarshalSSZMain.Post R Ri L bud e tp tl z bp len cap s s') ↔
    ((len.toNat = 32 →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
      Fv256.Spec.unmarshalSSZ ((List.range 32).map (fun i => s.mem.readLE (bp.toNat + i) 1)) = some (val256 s'.mem z.toNat) ∧
      MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) ∧
    (len.toNat ≠ 32 → Fv256.Arm64.UnmarshalSSZMain.ErrPost R Ri L bud e tp tl z bp len cap s s')) := by
  unfold Fv256.Arm64.UnmarshalSSZMain.Post Fv256.Arm64.UnmarshalSSZMain.SuccPost
  simp only [Janus.Spec.val256, Fv256.Proofs.Ssz.unmarshal_iff']
  try exact Iff.rfl

end Fv256.Arm64.UnmarshalSSZ.Bridge
