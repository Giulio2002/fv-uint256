import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.ScanSciBase
import Fv256.Spec.Arm64.ScanSciSpec
import Fv256.Spec.Arm64.ScanSpec
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.HexLemmas
import Fv256.Spec.IndexByteSpec
import Fv256.Spec.Core
import Fv256.Spec.B
import Fv256.Spec.B2
import Fv256.Spec.F
import Fv256.Spec.I
import Fv256.Spec.Scan
import Fv256.Spec.SumC64
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci

namespace Fv256.Arm64.Scan

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

end Fv256.Arm64.Scan

open Fv256.Arm64.CallSites
