import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge3
import Fv256.Spec.ToBig
import Fv256.Proofs.Arm64.ToBig

/-!
# arm64: `ToBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
open Fv256.Arm64.CallSites
open Fv256.Arm64.IntoBig (flagAddr bigType arrType BigObj)

namespace Fv256.Arm64.ToBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (z : BitVec 64) (s s' : State) :
    ((z.toNat = 0 → s'.regs 0 = 0) ∧
    (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat)])) ↔
    ((z.toNat = 0 → s'.regs 0 = 0) ∧
    (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ Fv256.Spec.BigIntAt s'.mem P (Fv256.Spec.toBig (val256 s.mem z.toNat))) ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat)])) := by
  simp only [Fv256.Proofs.Big.bigIntAt_iff]
  try exact Iff.rfl

end Fv256.Arm64.ToBig.Bridge
