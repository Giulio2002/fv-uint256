import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.PaddedBytes

/-!
# amd64: `PaddedBytes` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (z n : BitVec 64) (s s' : State) :
    (∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = n.toNat ∧ (s'.regs 1).toNat = n.toNat ∧
    (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
    Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) n.toNat = valueAt s z 32 % 2 ^ (8 * n.toNat) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) ↔
    (∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = n.toNat ∧ (s'.regs 1).toNat = n.toNat ∧
    (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
    (List.range n.toNat).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.paddedBytes (valueAt s z 32) n.toNat ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  simp only [← Fv256.Proofs.Bytes.mem_beBytes_iff_two]
  try exact Iff.rfl

end Fv256.Amd64.PaddedBytes.Bridge
