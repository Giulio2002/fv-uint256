import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Amd64.SfdTopSpec
import Fv256.Proofs.Amd64.SfdEnvC
import Fv256.Proofs.Amd64.FromDecimalSpec
import Fv256.Proofs.Amd64.UnmarshalSpec
import Fv256.Proofs.Common.DecCongr
import Fv256.Proofs.Amd64.UnmarshalDec
import Fv256.Proofs.Amd64.UnmarshalHex
import Fv256.Proofs.Amd64.FromHexLib
import Fv256.Spec.Amd64.UnmarshalTextS0

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalTextS

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

abbrev utEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).UnmarshalText"



end Fv256.Amd64.UnmarshalTextS
