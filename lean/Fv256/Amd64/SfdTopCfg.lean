import Fv256.Amd64.SfdProg
import Fv256.Amd64.SfdTopSpec

/-!
# `extCfg`: `SfdCfg` instantiated from the extraction (`Fv256.Amd64.SfdProg.dataAddr` / `contractAddr`)
-/

namespace Fv256.Amd64.SfdTopCfg

open Fv256.Amd64.SfdTopSpec

def extCfg : SfdCfg :=
  (Fv256.Amd64.SfdProg.cfgIoEOF,
   Fv256.Amd64.SfdProg.cfgErrBig,
   Fv256.Amd64.SfdProg.cfgMulTab,
   Fv256.Amd64.SfdProg.cfgNumErrType,
   Fv256.Amd64.SfdProg.cfgNumErrItab,
   Fv256.Amd64.SfdProg.cfgErrItab,
   Fv256.Amd64.SfdProg.cfgSynConst,
   Fv256.Amd64.SfdProg.cfgErrSyntax,
   Fv256.Amd64.SfdProg.cfgWbFlag,
   Fv256.Amd64.SfdProg.cfgFnStr,
   Fv256.Amd64.SfdProg.cfgMaxStr,
   Fv256.Amd64.SfdProg.cfgMallocgc,
   Fv256.Amd64.SfdProg.cfgMemmove,
   Fv256.Amd64.SfdProg.cfgNewobject,
   Fv256.Amd64.SfdProg.cfgWb1,
   Fv256.Amd64.SfdProg.cfgWb2)

end Fv256.Amd64.SfdTopCfg
