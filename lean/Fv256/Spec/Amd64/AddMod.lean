import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.AddMod

abbrev Pre (z x y m : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x300 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x348 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16) ∧
        ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16)

end Fv256.Amd64.AddMod
