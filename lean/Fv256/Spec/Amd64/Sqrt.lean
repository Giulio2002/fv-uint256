import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x200 ∧ 0x280 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1f0 0x18 ∧ Buffer s z 32 true ∧
    Buffer s x 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ x.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x18 ≤ (s.regs regG).toNat + 16)

end Fv256.Amd64.Sqrt
