import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulModWithReciprocalCore

abbrev Pre (z x m mu : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x2d0 ∧ 0x328 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x320 8 ∧
    Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
    Apart z.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
    Apart x.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
    Apart m.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
        Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
        Fv256.F.MuOK (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
    Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x320) 0x328

end Fv256.Amd64.IMulModWithReciprocalCore
