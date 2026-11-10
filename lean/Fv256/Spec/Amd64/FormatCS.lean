import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Amd64.FormatNil
import Fv256.Spec.Amd64.FormatWitA
import Fv256.Spec.FormatFastDefs
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.C
import Fv256.Spec.E
import Fv256.Spec.FormatBytes

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Toy

open Janus.Contracts.IfaceModel Janus.Spec.Type

open Fv256.Amd64.FormatWitA Fv256.CallSites

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option maxRecDepth 100000

namespace Fv256.Amd64.FormatCS

/-- the precondition of `runtime.typeAssert` as one conjunct (the contract's own `pre`) -/
@[reducible] def TypeAssertSite (R : IfaceModel) (H : RtReady) (s : State) : Prop :=
  Janus.Contracts.IfaceAmd64.RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      (s.regs 3).toNat ≠ 0 ∧
      ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 3).toNat).isSome)) ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s

end Fv256.Amd64.FormatCS
