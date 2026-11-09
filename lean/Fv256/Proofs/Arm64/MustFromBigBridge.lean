import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Proofs.Common.BigBridge2
import Fv256.Spec.MustFromBig

/-!
# arm64: `MustFromBig` postcondition bridges (readable `Spec.mustFromBig` / `Spec.setFromBig` form versus the proof's `Fv256.C` form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

namespace Fv256.Arm64.MustFromBig.Bridge

/-- The returning-case postcondition as the proof states it is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) :
    ((x.toNat = 0 ∨ len.toNat ≤ 4) ∧
        (x.toNat = 0 → s'.regs 0 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))) ↔
    (let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  (x.toNat = 0 ∨ (Fv256.Spec.mustFromBig b len.toNat).isSome) ∧
  (x.toNat = 0 → s'.regs 0 = 0) ∧
  (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
    s'.mem.accessible ptr 32 true = true ∧
    val256 s'.mem ptr = Fv256.Spec.setFromBig b ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))) := by
  simp only [Fv256.Proofs.Big.isSome_mustFromBig, Fv256.Proofs.Big.setFromBig_bigValue]
  try exact Iff.rfl

/-- The panic condition as the proof states it (`4 < len`) is the readable one (`Spec.mustFromBig = none`). -/
theorem pan_iff (x pw len : BitVec 64) (s : State) (v : Eface) :
    (x.toNat ≠ 0 ∧ 4 < len.toNat ∧ v = ⟨panicType, panicData⟩) ↔
    (let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  x.toNat ≠ 0 ∧ (Fv256.Spec.mustFromBig b len.toNat).isNone ∧ v = ⟨panicType, panicData⟩) := by
  simp only [Fv256.Proofs.Big.isNone_mustFromBig]
  try exact Iff.rfl

end Fv256.Arm64.MustFromBig.Bridge
