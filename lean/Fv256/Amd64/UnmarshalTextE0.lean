import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.UnmarshalSpec
import Fv256.DecCongr
import Fv256.Amd64.UnmarshalDec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.FromHexLib

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalText

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
    Extracted.dataAddr.«.rodata#3d2a826c»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»


end Fv256.Amd64.UnmarshalText
