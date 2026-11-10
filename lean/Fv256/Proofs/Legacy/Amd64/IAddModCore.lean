import Extracted
import Fv256.Spec.Core
import Fv256.Proofs.Legacy.B
import Fv256.Proofs.Legacy.B2
import Fv256.Proofs.Legacy.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IAddModCore

abbrev Pre (z x m : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x330 ∧ 0x3b0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x10 ∧ Buffer s z 32 true ∧
    Buffer s x 32 false ∧ Buffer s m 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ m.toNat) ∧
    (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
    ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16) ∧
    Extracted.program.DataLoaded s.mem

end Fv256.Amd64.IAddModCore
