import Extracted
import Fv256.Amd64.SfdTopSpec

/-!
# `extCfg`: `SfdCfg` instantiated from the extraction (`Extracted.dataAddr` / `contractAddr`)
-/

namespace Fv256.Amd64.SfdTopCfg

open Fv256.Amd64.SfdTopSpec

def extCfg : SfdCfg :=
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

end Fv256.Amd64.SfdTopCfg
