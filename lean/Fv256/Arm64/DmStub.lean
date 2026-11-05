import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.UdivremD
import Fv256.Arm64.UdivremF
import Fv256.Arm64.KnuthSummary

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.DmStub
theorem correctness : True := trivial
end Fv256.Arm64.DmStub
