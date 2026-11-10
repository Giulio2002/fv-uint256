import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.MarshalSSZ

/-!
# amd64: `MarshalSSZ` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.MarshalSSZ.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) :
    (∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 32 ∧ (s'.regs 1).toNat = 32 ∧
    s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
    s'.mem.readLE ptr 32 = valueAt s z 32 ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) ↔
    (∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 32 ∧ (s'.regs 1).toNat = 32 ∧
    s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
    (List.range 32).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.marshalSSZ (valueAt s z 32) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  simp only [valueAt, ← Fv256.Proofs.Bytes.mem_leBytes_iff_rd]
  try exact Iff.rfl

end Fv256.Amd64.MarshalSSZ.Bridge
