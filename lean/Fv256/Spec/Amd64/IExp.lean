import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IExp

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x48 ∧ 0x128 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xd0 0x10 ∧ Buffer s z 32 true ∧
        Buffer s x 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem

end Fv256.Amd64.IExp
