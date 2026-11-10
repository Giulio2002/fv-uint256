import Extracted
import Fv256.Proofs.Legacy.RecipSpec
import Fv256.Spec.Core
import Fv256.Proofs.Legacy.B
import Fv256.Proofs.Legacy.B2
import Fv256.Proofs.Legacy.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulModCore

abbrev Pre (z x m : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x320 ∧ 0x3b0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x3a8 8 ∧
    Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s m 32 false ∧
    Apart z.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
    Apart x.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
    Apart m.toNat 32 (((s.regs regSP).toNat) - 0x3a8) 0x3b0 ∧
    Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x3a8) 0x3b0

end Fv256.Amd64.IMulModCore
