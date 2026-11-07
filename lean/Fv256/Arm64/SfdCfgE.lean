import Extracted
import Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SetFromDecimal

/-- the addresses of this extraction -/
def cfgE : SfdCfg := SfdCfg.mk
  (Extracted.dataAddr.«io.EOF»)
  (Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»)
  (Extracted.dataAddr.«github.com/holiman/uint256.multipliers»)
  (Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»)
  (Extracted.dataAddr.«go:itab.*strconv.NumError,error»)
  (Extracted.dataAddr.«go:itab.internal/strconv.Error,error»)
  (Extracted.dataAddr.«.rodata#9967e7a3»)
  (Extracted.dataAddr.«strconv.ErrSyntax»)
  (Extracted.dataAddr.«runtime.writeBarrier»)
  (Extracted.dataAddr.«.rodata#7233b75a»)
  (Extracted.dataAddr.«.rodata#575028b4»)
  (Extracted.program.contractAddr "runtime.mallocgc")
  (Extracted.program.contractAddr "runtime.memmove")
  (Extracted.program.contractAddr "runtime.newobject")
  (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
  (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

end Fv256.Arm64.SetFromDecimal
