import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Amd64.SqrtLibBase
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.SqrtMath
import Fv256.Proofs.Common.SqrtHead
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.LshProg
import Fv256.Proofs.Common.RshProg
import Fv256.Proofs.Amd64.LshSumAlias
import Fv256.Proofs.Amd64.RshSum
import Fv256.Proofs.Amd64.SqrtSumL
import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SqrtLib

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Fv256.SqrtProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcRsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.RshProg.program Fv256.SqrtProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.SqrtProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

end Fv256.Amd64.SqrtLib
