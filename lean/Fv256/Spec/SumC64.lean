import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.C

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- what a leaf callee preserves. -/
def Kept (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
    s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase

end Fv256.C
