import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Common.SszBridge
import Fv256.Spec.UnmarshalSSZ
import Fv256.Proofs.Amd64.UnmarshalSSZMain

/-!
# amd64: `UnmarshalSSZ` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf

namespace Fv256.Amd64.UnmarshalSSZ.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) :
    (Fv256.Amd64.UnmarshalSSZMain.Post R Ri L bud e tp tl z bp len cap s s') ↔
    ((len.toNat = 32 →
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧
      Fv256.Spec.unmarshalSSZ ((List.range 32).map (fun i => s.mem.readLE (bp.toNat + i) 1)) = some (s'.mem.readLE z.toNat 32) ∧
      Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
        ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]) ∧
    (len.toNat ≠ 32 → Fv256.Amd64.UnmarshalSSZMain.ErrPost R Ri L bud e tp tl z bp len cap s s')) := by
  unfold Fv256.Amd64.UnmarshalSSZMain.Post Fv256.Amd64.UnmarshalSSZMain.SuccPost
  simp only [Fv256.Proofs.Ssz.unmarshal_iff']
  try exact Iff.rfl

end Fv256.Amd64.UnmarshalSSZ.Bridge
