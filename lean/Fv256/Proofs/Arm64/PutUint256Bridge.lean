import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.PutUint256

/-!
# arm64: `PutUint256` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.PutUint256.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z ptr : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (ptr.toNat + i) 1) 32 = val256 s.mem z.toNat ∧
    Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 (s.sp.toNat - 24) 48) ↔
    ((List.range 32).map (fun i => s'.mem.readLE (ptr.toNat + i) 1) = Fv256.Spec.putUint256 (val256 s.mem z.toNat) ∧
    Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 (s.sp.toNat - 24) 48) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff' s'.mem _ 32 _ (by simpa [Janus.Spec.val256] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)).symm Iff.rfl

end Fv256.Arm64.PutUint256.Bridge
