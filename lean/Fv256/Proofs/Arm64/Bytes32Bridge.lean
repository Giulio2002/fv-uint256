import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.Bytes32

/-!
# arm64: `Bytes32` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Bytes32.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) 32 = val256 s.mem z.toNat ∧
    Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 56) 56) ↔
    ((List.range 32).map (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) = Fv256.Spec.bytes32 (val256 s.mem z.toNat) ∧
    Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 56) 56) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff' s'.mem _ 32 _ (by simpa [Janus.Spec.val256] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)).symm Iff.rfl

end Fv256.Arm64.Bytes32.Bridge
