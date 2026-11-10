import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BytesBridge
import Fv256.Spec.Bytes
import Fv256.Proofs.Arm64.Bytes

/-!
# arm64: `Bytes` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Bytes.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) :
    (∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
    (s'.regs 0).toNat = ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) ∧
    (s'.regs 1).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧ (s'.regs 2).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧
    Spec.fromBE (fun i => s'.mem.readLE (ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) + i) 1) (Spec.byteLen (val256 s.mem z.toNat)) = val256 s.mem z.toNat ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4176, s.sp.toNat + 24)])) ↔
    (let v := val256 s.mem z.toNat
    let n := Fv256.Spec.minBytes v
    let off := if n = 0 then 0 else 32 - n
    ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
      (s'.regs 0).toNat = ptr + off ∧ (s'.regs 1).toNat = n ∧ (s'.regs 2).toNat = n ∧
      (List.range n).map (fun i => s'.mem.readLE (ptr + off + i) 1) = Fv256.Spec.bytes v ∧
      MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4176, s.sp.toNat + 24)])) := by
  simp only [← Fv256.Proofs.Bytes.minBytes_eq_byteLen, ← Fv256.Proofs.Bytes.mem_bytes_iff]
  try exact Iff.rfl

end Fv256.Arm64.Bytes.Bridge
