import Extracted
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Amd64.FromHexLib

/-!
# `hhex` discharged: the `fromHex` summary of the library program `FromHexProg` moved to `Extracted.program.link impl`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalHexDisch

set_option maxRecDepth 200000 in
theorem hcHex : Janus.Contracts.EqHashModel.CodeIn64 Fv256.FromHexProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem fh_eq : Fv256.Amd64.FromHexLib.fh = 4922368 := by decide

theorem hhex_of (impl : List Janus.Amd64.Segment) : ∀ (z hp len : BitVec 64),
    Summary (Extracted.program.link impl) 4922368 (FromHexPre z hp len) (FromHexPost z hp len) := by
  intro z hp len
  rw [← fh_eq]
  exact Fv256.CodeIn.lib_summary_link impl hcHex (fromHex_lib z hp len)

end Fv256.Amd64.UnmarshalHexDisch
