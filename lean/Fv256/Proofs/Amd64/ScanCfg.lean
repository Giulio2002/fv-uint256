import Extracted
import Fv256.Proofs.Amd64.SfdTopSpec
import Fv256.Spec.Amd64.ScanCfg

/-!
# `cfg`: `SfdCfg` instantiated from the Scan extraction (`Extracted.dataAddr` / `contractAddr`), and the other addresses of the statement
-/

namespace Fv256.Amd64.ScanCfg

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.SfdTopSpec

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"
abbrev sci : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).scanScientificFromString"
abbrev expEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Exp"
abbrev moEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).MulOverflow"
abbrev ibsEntry : Nat := segAddr Extracted.program "internal/bytealg.IndexByteString.abi0"
end Fv256.Amd64.ScanCfg
