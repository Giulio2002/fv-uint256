import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Spec.FromBig

/-!
# arm64: `FromBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.FromBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) :
    ((x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 1 = 0) ∧
    (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 32 true = true ∧
      val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
        (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
      (s'.regs 1).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
      MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))) ↔
    (let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
    let r := Fv256.Spec.fromBig b len.toNat
    (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 1 = 0) ∧
    (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
      s'.mem.accessible ptr 32 true = true ∧
      val256 s'.mem ptr = r.1 ∧ (s'.regs 1).toNat = (if r.2 then 1 else 0) ∧
      MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))) := by
  simp only [Fv256.Spec.fromBig, Fv256.Proofs.Big.setFromBig_bigValue]
  try exact Iff.rfl

end Fv256.Arm64.FromBig.Bridge
