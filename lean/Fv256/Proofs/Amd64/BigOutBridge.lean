import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge3
import Fv256.Spec.IntoBig
import Fv256.Proofs.Amd64.IntoBig

/-!
# amd64: `IntoBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (R : RtInv) (z bp : BitVec 64) (s s' : State) :
    (Post R z bp s s') ↔
    ((z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
    (z.toNat ≠ 0 → ∃ P : Nat, Fv256.Spec.BigIntSlot s'.mem bp.toNat P (Fv256.Spec.intoBig (val256 s.mem z.toNat))) ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8),
      (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
      (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
    (s.mem.readLE bp.toNat 8 = 0 →
      MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
        (bp.toNat, bp.toNat + 8)]))) := by
  unfold Fv256.Amd64.IntoBig.Post
  simp only [Fv256.Proofs.Big.bigIntSlot_iff]
  try exact Iff.rfl

end Fv256.Amd64.IntoBig.Bridge
