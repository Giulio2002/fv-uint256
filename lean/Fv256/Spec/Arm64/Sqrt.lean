import Extracted
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Sqrt

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => GuardOK s 448 ∧ StackOK s 488 24 ∧ 488 ≤ s.sp.toNat ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
    Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
    Disjoint z.toNat 32 (s.sp.toNat - 488) 512 ∧ Disjoint x.toNat 32 (s.sp.toNat - 488) 512

end Fv256.Arm64.Sqrt
