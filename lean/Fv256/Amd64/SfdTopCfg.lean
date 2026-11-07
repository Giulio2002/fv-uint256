import Fv256.Amd64.SfdProg
import Fv256.Amd64.SfdTopSpec

/-!
# `extCfg`: `SfdCfg` instantiated from the extraction (`Fv256.Amd64.SfdProg.dataAddr` / `contractAddr`)
-/

namespace Fv256.Amd64.SfdTopCfg

open Fv256.Amd64.SfdTopSpec

def extCfg : SfdCfg :=
  (Fv256.Amd64.SfdProg.dataAddr.«io.EOF»,
   Fv256.Amd64.SfdProg.dataAddr.«github.com/holiman/uint256.ErrBig256Range»,
   Fv256.Amd64.SfdProg.dataAddr.«github.com/holiman/uint256.multipliers»,
   Fv256.Amd64.SfdProg.dataAddr.«type:strconv.NumError#3eb4e62e»,
   Fv256.Amd64.SfdProg.dataAddr.«go:itab.*strconv.NumError,error»,
   Fv256.Amd64.SfdProg.dataAddr.«go:itab.internal/strconv.Error,error»,
   Fv256.Amd64.SfdProg.dataAddr.«.rodata#9967e7a3»,
   Fv256.Amd64.SfdProg.dataAddr.«strconv.ErrSyntax»,
   Fv256.Amd64.SfdProg.dataAddr.«runtime.writeBarrier»,
   Fv256.Amd64.SfdProg.dataAddr.«.rodata#3d2a826c»,
   Fv256.Amd64.SfdProg.dataAddr.«.rodata#575028b4»,
   Fv256.Amd64.SfdProg.program.contractAddr "runtime.mallocgc",
   Fv256.Amd64.SfdProg.program.contractAddr "runtime.memmove",
   Fv256.Amd64.SfdProg.program.contractAddr "runtime.newobject",
   Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1",
   Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2")

end Fv256.Amd64.SfdTopCfg
