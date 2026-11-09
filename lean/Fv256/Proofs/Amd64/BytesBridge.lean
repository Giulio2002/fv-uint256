import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.Bytes

/-!
# amd64: `Bytes` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.Bytes.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) :
    (∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
    (s'.regs 0).toNat = ptr + (if Spec.byteLen (valueAt s z 32) = 0 then 0 else 32 - Spec.byteLen (valueAt s z 32)) ∧
    (s'.regs 3).toNat = Spec.byteLen (valueAt s z 32) ∧ (s'.regs 1).toNat = Spec.byteLen (valueAt s z 32) ∧
    Spec.fromBE (fun i => s'.mem.readLE (ptr + (if Spec.byteLen (valueAt s z 32) = 0 then 0 else 32 - Spec.byteLen (valueAt s z 32)) + i) 1) (Spec.byteLen (valueAt s z 32)) = valueAt s z 32 ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)])) ↔
    (let v := valueAt s z 32
    let n := Fv256.Spec.minBytes v
    let off := if n = 0 then 0 else 32 - n
    ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
      (s'.regs 0).toNat = ptr + off ∧ (s'.regs 3).toNat = n ∧ (s'.regs 1).toNat = n ∧
      (List.range n).map (fun i => s'.mem.readLE (ptr + off + i) 1) = Fv256.Spec.bytes v ∧
      MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 24)])) := by
  simp only [← Fv256.Proofs.Bytes.minBytes_eq_byteLen, ← Fv256.Proofs.Bytes.mem_bytes_iff]
  try exact Iff.rfl

end Fv256.Amd64.Bytes.Bridge
