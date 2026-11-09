import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ISqrt

abbrev Pre (z : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x220 ∧ 0x2a0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x210 0x10 ∧ Buffer s z 32 true ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

end Fv256.Amd64.ISqrt
