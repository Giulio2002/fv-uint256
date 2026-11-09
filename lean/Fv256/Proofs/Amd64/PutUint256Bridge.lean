import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.PutUint256

/-!
# amd64: `PutUint256` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.PutUint256.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z ptr : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (ptr.toNat + i) 1) 32 = valueAt s z 32 ∧
    Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 ((s.regs regSP).toNat - 8) 32) ↔
    ((List.range 32).map (fun i => s'.mem.readLE (ptr.toNat + i) 1) = Fv256.Spec.putUint256 (valueAt s z 32) ∧
    Fv256.Util.OnlyWrites2 s.mem s'.mem ptr.toNat 32 ((s.regs regSP).toNat - 8) 32) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff' s'.mem _ 32 _ (by simpa [valueAt] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)).symm Iff.rfl

end Fv256.Amd64.PutUint256.Bridge
