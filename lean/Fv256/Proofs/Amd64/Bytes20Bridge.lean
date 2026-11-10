import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.Bytes20

/-!
# amd64: `Bytes20` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Bytes20.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z : BitVec 64) (s s' : State) :
    (Spec.fromBE (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) 20 = valueAt s z 32 % 2 ^ 160 ∧
    Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 20 ((s.regs regSP).toNat - 40) 40) ↔
    ((List.range 20).map (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) = Fv256.Spec.bytes20 (valueAt s z 32) ∧
    Fv256.Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 20 ((s.regs regSP).toNat - 40) 40) := by
  exact and_congr (Fv256.Proofs.Bytes.mem_beBytes_iff_two s'.mem _ _ _).symm Iff.rfl

end Fv256.Amd64.Bytes20.Bridge
