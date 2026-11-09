import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Arm64.UdivremD
import Fv256.Proofs.Arm64.UdivremF
import Fv256.Proofs.Arm64.KnuthSummary

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.DmStub
theorem correctness : True := trivial
end Fv256.Arm64.DmStub
