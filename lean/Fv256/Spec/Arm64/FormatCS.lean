import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.FM.IntoBigDefs
import Fv256.Spec.Arm64.FormatNil
import Fv256.Spec.FormatFastDefsA64
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.FormatBytes

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Toy

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Janus.Spec.Type Janus.Contracts.Iface

open Fv256.Arm64.CallSites

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option maxRecDepth 100000

namespace Fv256.Arm64.FormatCS

/-- the precondition of `runtime.typeAssert` as one conjunct (the contract's own `pre`) -/
@[reducible] def TypeAssertSite (R : IfaceModel) (H : RtReady) (s : State) : Prop :=
  RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      (s.regs 1).toNat ≠ 0 ∧
      ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 1).toNat).isSome)) ∧
      Ready H R.priv [(s.regs 0).toNat, (s.regs 1).toNat] s

end Fv256.Arm64.FormatCS
