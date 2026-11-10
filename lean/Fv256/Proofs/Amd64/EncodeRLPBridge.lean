import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Spec.EncodeRLP
import Fv256.Proofs.Amd64.EncodeRLP

/-!
# amd64: `EncodeRLP` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (stack : Nat) (R : Res) (z w : BitVec 64) (s s' : State) :
    ((∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2) ∧
    (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)])) ↔
    ((∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2) ∧
    (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)])) := by
  exact Iff.rfl

end Fv256.Amd64.EncodeRLP.Bridge
