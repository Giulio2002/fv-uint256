import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Amd64.DecExt
import Fv256.Spec.Amd64.FM.IntoBigDefs
import Fv256.Spec.Amd64.FormatBigDefs
import Fv256.Spec.Amd64.FormatCS
import Fv256.Spec.Amd64.FormatFastPre
import Fv256.Spec.Amd64.FormatNil
import Fv256.Spec.Amd64.FormatTransfer
import Fv256.Spec.Amd64.FormatWitA
import Fv256.Spec.FormatFastDefs
import Fv256.Spec.HexLemmas
import Janus
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel

open Fv256.FormatFast Fv256.Amd64.FormatTransfer Fv256.Amd64.FormatFast

open Janus.Spec.Type (IfaceModel)

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace Fv256.Amd64.Format

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

end Fv256.Amd64.Format
