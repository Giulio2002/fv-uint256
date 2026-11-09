import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.HashTreeRoot

/-!
# arm64: `HashTreeRoot` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.HashTreeRoot.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z : BitVec 64) (s s' : State) :
    (s'.mem.readLE (s.sp.toNat + 8) 32 = val256 s.mem z.toNat ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
    Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 88) 88) ↔
    ((List.range 32).map (fun i => s'.mem.readLE (s.sp.toNat + 8 + i) 1) = Fv256.Spec.hashTreeRoot (val256 s.mem z.toNat) ∧
    s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
    Util.OnlyWrites2 s.mem s'.mem (s.sp.toNat + 8) 32 (s.sp.toNat - 88) 88) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_leBytes_iff' s'.mem _ 32 _ (by simpa [Janus.Spec.val256] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)).symm Iff.rfl

end Fv256.Arm64.HashTreeRoot.Bridge
