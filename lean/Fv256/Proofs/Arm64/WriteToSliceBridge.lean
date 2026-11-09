import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.WriteToSlice

/-!
# arm64: `WriteToSlice` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToSlice.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z d len : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
      val256 s.mem z.toNat % 2 ^ (8 * min len.toNat 32) ∧
    Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) (s.sp.toNat - 24) 48) ↔
    ((List.range (min len.toNat 32)).map (fun i => s'.mem.readLE (d.toNat + i) 1) = Fv256.Spec.writeToSlice (val256 s.mem z.toNat) len.toNat ∧
    Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) (s.sp.toNat - 24) 48) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff_two s'.mem _ _ _).symm Iff.rfl

end Fv256.Arm64.WriteToSlice.Bridge
