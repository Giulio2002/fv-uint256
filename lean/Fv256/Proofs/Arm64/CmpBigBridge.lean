import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.BigBridge
import Fv256.Spec.CmpBig

/-!
# arm64: `CmpBig` postcondition bridge (readable byte-list form versus the proof's number-reading form)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.CmpBig.Bridge

/-- The postcondition as the proof states it (number-reading form) is equivalent to the claim's readable form (`Post`). -/
theorem post_iff (z x pw len : BitVec 64) (s s' : State) :
    (s'.regs 0 = BitVec.ofInt 64
      (Fv256.C.cmpBig (val256 s.mem z.toNat)
        (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
          (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat))) ∧
    MemFrame s.mem s'.mem [(s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat - 72, s.sp.toNat)]) ↔
    (s'.regs 0 = BitVec.ofInt 64
      (Fv256.Spec.cmpBig (val256 s.mem z.toNat) (Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat)) ∧
    MemFrame s.mem s'.mem [(s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat - 72, s.sp.toNat)]) := by
  simp only [Fv256.Proofs.Big.cmpBig_bigValue]
  try exact Iff.rfl

end Fv256.Arm64.CmpBig.Bridge
