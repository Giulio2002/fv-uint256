import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Spec.FromBig

/-!
# amd64: `FromBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.FromBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) :
    ((x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
    (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 32 true = true ∧
      s'.mem.readLE ptr 32 =
        Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
          (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
      (s'.regs 3).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
      MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))) ↔
    (let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
    let r := Fv256.Spec.fromBig b len.toNat
    (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
    (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 32 true = true ∧
      s'.mem.readLE ptr 32 = r.1 ∧ (s'.regs 3).toNat % 256 = (if r.2 then 1 else 0) ∧
      MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))) := by
  simp only [Fv256.Spec.fromBig, Fv256.Proofs.Big.setFromBig_bigValue]
  try exact Iff.rfl

end Fv256.Amd64.FromBig.Bridge
