import Extracted
import Fv256.Amd64.SfdTopSpec

/-!
# `cfg`: `SfdCfg` instantiated from the Scan extraction (`Extracted.dataAddr` / `contractAddr`), and the other addresses of the statement
-/

namespace Fv256.Amd64.ScanCfg

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.SfdTopSpec

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
abbrev sci : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).scanScientificFromString"
abbrev expEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Exp"
abbrev moEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).MulOverflow"
abbrev ibsEntry : Nat := segAddr Extracted.program "internal/bytealg.IndexByteString.abi0"
abbrev avxAddr : Nat := Extracted.dataAddr.«internal/cpu.X86» + 68
abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

end Fv256.Amd64.ScanCfg
