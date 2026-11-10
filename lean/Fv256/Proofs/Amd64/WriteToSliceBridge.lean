import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.WriteToSlice

/-!
# amd64: `WriteToSlice` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToSlice.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z d len : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
      valueAt s z 32 % 2 ^ (8 * min len.toNat 32) ∧
    Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) ((s.regs regSP).toNat - 8) 32) ↔
    ((List.range (min len.toNat 32)).map (fun i => s'.mem.readLE (d.toNat + i) 1) = Fv256.Spec.writeToSlice (valueAt s z 32) len.toNat ∧
    Fv256.Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) ((s.regs regSP).toNat - 8) 32) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff_two s'.mem _ _ _).symm Iff.rfl

end Fv256.Amd64.WriteToSlice.Bridge
