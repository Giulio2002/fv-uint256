import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Spec.CmpBig

/-!
# amd64: `CmpBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic

namespace Fv256.Amd64.CmpBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z x pw len : BitVec 64) (s s' : State) :
    (s'.regs 0 = BitVec.ofInt 64
      (Fv256.C.cmpBig (valueAt s z 32)
        (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
          (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat))) ∧
    Janus.MemFrame s.mem s'.mem [((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 16),
      ((s.regs regSP).toNat - 72, (s.regs regSP).toNat)]) ↔
    (s'.regs 0 = BitVec.ofInt 64
      (Fv256.Spec.cmpBig (valueAt s z 32) (Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat)) ∧
    Janus.MemFrame s.mem s'.mem [((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 16),
      ((s.regs regSP).toNat - 72, (s.regs regSP).toNat)]) := by
  simp only [Fv256.Proofs.Big.cmpBig_bigValue]
  try exact Iff.rfl

end Fv256.Amd64.CmpBig.Bridge
