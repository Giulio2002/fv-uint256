import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IExp

abbrev Pre (z e : BitVec 64) : State → Prop :=
  fun s => GuardOK s 80 ∧ StackOK s 216 8 ∧ 384 ≤ s.sp.toNat ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 216 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    Ptr32 s.mem z true ∧ Ptr32 s.mem e false ∧
    Disjoint z.toNat 32 (s.sp.toNat - 216) 208 ∧ Disjoint e.toNat 32 (s.sp.toNat - 216) 208 ∧ Extracted.program.DataLoaded s.mem

end Fv256.Arm64.IExp
