import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.IndexByteSpec
import Fv256.Spec.Core
import Fv256.Spec.F
import Fv256.Spec.I
import Fv256.Spec.Scan
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.ScanSciSpec

variable (C : SfdCfg)

/-- package-initialisation facts about the sentinel errors (as `FromDecimalSpec.InitDone`) -/
def InitDone (R2 : IfaceModel) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE C.ioEOF 8 ≠ 0 ∧ m.readLE (C.ioEOF + 8) 8 ≠ 0 ∧ m.readLE C.errBig 8 ≠ 0 ∧ m.readLE (C.errBig + 8) 8 ≠ 0 ∧
  (∀ r ∈ R2.priv, r.1 ≤ r.2)

section cases

open Fv256.ScanSpec

end cases

end Fv256.Arm64.ScanSciSpec
