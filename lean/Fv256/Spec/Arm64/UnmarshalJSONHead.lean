import Extracted
import Fv256.Spec.Arm64.FromHexLib
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.UnmarshalHex
import Fv256.Spec.Arm64.UnmarshalSpecJ
import Fv256.Spec.Arm64.UnmarshalSpec
import Fv256.Spec.Core
import Fv256.Spec.I
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalSpecJ Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalJPost

namespace Fv256.Arm64.UnmarshalJSON

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg :=
  (Extracted.dataAddr.«io.EOF»,
    Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»,
    Extracted.dataAddr.«github.com/holiman/uint256.multipliers»,
    Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»,
    Extracted.dataAddr.«go:itab.*strconv.NumError,error»,
    Extracted.dataAddr.«go:itab.internal/strconv.Error,error»,
    Extracted.dataAddr.«.rodata#9967e7a3»,
    Extracted.dataAddr.«strconv.ErrSyntax»,
    Extracted.dataAddr.«runtime.writeBarrier»,
    Extracted.dataAddr.«.rodata#7233b75a»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

end Fv256.Arm64.UnmarshalJSON
