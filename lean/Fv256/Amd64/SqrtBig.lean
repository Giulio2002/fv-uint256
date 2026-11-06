import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath
import Fv256.SqrtHead
import Fv256.SpecB
import Fv256.UtilB
import Fv256.CodeIn
import Fv256.LshProg
import Fv256.RshProg
import Fv256.Amd64.LshSumAlias
import Fv256.Amd64.RshSum
import Fv256.Amd64.SqrtSum
import Fv256.ChainProg
import Fv256.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcRsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.RshProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

end Fv256.Amd64.Sqrt
