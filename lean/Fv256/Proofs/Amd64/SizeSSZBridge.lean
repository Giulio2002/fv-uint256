import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.SizeSSZ

/-!
# amd64: `SizeSSZ` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SizeSSZ.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff  (s s' : State) :
    ((s'.regs 0).toNat = Spec.sizeSSZ) ↔
    ((s'.regs 0).toNat = Fv256.Spec.sizeSSZ) := by
  exact Iff.rfl

end Fv256.Amd64.SizeSSZ.Bridge
