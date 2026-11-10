import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.DecExt
import Fv256.Spec.Arm64.FM.IntoBigDefs
import Fv256.Spec.Arm64.FormatCS
import Fv256.Spec.Arm64.FormatNil
import Fv256.Spec.Arm64.FormatTransfer
import Fv256.Spec.FormatFastDefsA64
import Fv256.Spec.HexLemmas
import Janus
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel

open Fv256.FormatFastA64 Fv256.Arm64.FormatTransfer

open Janus.Spec.Type (IfaceModel)

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace Fv256.Arm64.Format

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

end Fv256.Arm64.Format
