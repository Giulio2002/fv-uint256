import Extracted
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.LshProg

namespace Fv256.Amd64.Float64

set_option maxRecDepth 100000 in
theorem hcLsh : Janus.Contracts.EqHashModel.CodeIn64 Fv256.LshProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

end Fv256.Amd64.Float64
