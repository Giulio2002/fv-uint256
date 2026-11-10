import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.WriteToArray32

/-!
# amd64: `WriteToArray32` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToArray32.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z dest : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (dest.toNat + i) 1) 32 = valueAt s z 32 ∧
    Janus.Spec.OnlyWrites s.mem s'.mem dest.toNat 32) ↔
    ((List.range 32).map (fun i => s'.mem.readLE (dest.toNat + i) 1) = Fv256.Spec.writeToArray32 (valueAt s z 32) ∧
    Janus.Spec.OnlyWrites s.mem s'.mem dest.toNat 32) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff' s'.mem _ 32 _ (by simpa [valueAt] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)).symm Iff.rfl

end Fv256.Amd64.WriteToArray32.Bridge
