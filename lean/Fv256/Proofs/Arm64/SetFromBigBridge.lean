import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Spec.SetFromBig

/-!
# arm64: `SetFromBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetFromBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z b pw len : BitVec 64) (s s' : State) :
    ((s'.regs 0).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
    val256 s'.mem z.toNat =
      Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
        (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
    OnlyWrites s.mem s'.mem z.toNat 32) ↔
    ((s'.regs 0).toNat = (if Fv256.Spec.setFromBigOverflow len.toNat then 1 else 0) ∧
    val256 s'.mem z.toNat = Fv256.Spec.setFromBig (Fv256.Spec.bigValue (s.mem.readLE b.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
    OnlyWrites s.mem s'.mem z.toNat 32) := by
  simp only [Fv256.Proofs.Big.setFromBig_bigValue]
  try exact Iff.rfl

end Fv256.Arm64.SetFromBig.Bridge
