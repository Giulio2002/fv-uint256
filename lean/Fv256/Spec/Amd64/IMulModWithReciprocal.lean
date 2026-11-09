import Extracted
import Fv256.Spec.Amd64.IMulModWithReciprocalCore
import Fv256.Spec.Core
import Fv256.Spec.F
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

set_option exponentiation.threshold 600

namespace Fv256.Amd64.IMulModWithReciprocal

abbrev Pre := Fv256.Amd64.IMulModWithReciprocalCore.Pre

end Fv256.Amd64.IMulModWithReciprocal
