import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge3
import Fv256.Spec.ToBig
import Fv256.Proofs.Amd64.ToBig

/-!
# amd64: `ToBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
open Fv256.Amd64.IntoBig (flagAddr bigType arrType BigObj)

namespace Fv256.Amd64.ToBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (z : BitVec 64) (s s' : State) :
    ((z.toNat = 0 → s'.regs 0 = 0) ∧
    (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)])) ↔
    ((z.toNat = 0 → s'.regs 0 = 0) ∧
    (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ Fv256.Spec.BigIntAt s'.mem P (Fv256.Spec.toBig (val256 s.mem z.toNat))) ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)])) := by
  simp only [Fv256.Proofs.Big.bigIntAt_iff]
  try exact Iff.rfl

end Fv256.Amd64.ToBig.Bridge
