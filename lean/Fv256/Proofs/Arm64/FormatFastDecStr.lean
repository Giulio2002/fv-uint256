import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Arm64.DecExt
import Fv256.Proofs.Arm64.DecT

open Janus Janus.Arm64 Janus.GoABI Janus.Contracts
open Fv256.E Fv256.Arm64.Dec

namespace Fv256.Arm64.FormatFast

/-- the string `Dec` returns lies outside a writable window that is outside the runtime ranges, and above the zero page -/
theorem dec_str_out {rt : List (Nat × Nat)} {M : Janus.Arm64.Memory} {a n p l : Nat}
    (hdl : Extracted.program.DataLoaded M) (hwa : M.accessible a n true = true) (hout : Outside a n rt)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1) (hDA : DecAt rt 989280 1002589 960826 p l) :
    (p + l ≤ a ∨ a + n ≤ p) ∧ 32 ≤ p := by
  have hdL := Fv256.Arm64.LinkEq.DataLoaded.of_subset hLib.data hdl
  have hj1 := Fv256.FormatFastA64.dataLoaded_disjoint hdL digits_mem hwa
  have hj2 := Fv256.FormatFastA64.dataLoaded_disjoint hdL smalls_mem hwa
  have hj3 := Fv256.FormatFastA64.dataLoaded_disjoint hdL zeroDat_mem hwa
  rw [digits_base, digits_len] at hj1
  rw [smalls_base, smalls_len] at hj2
  rw [zeroDat_base, zeroDat_len] at hj3
  rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := MemFrame.outside_mem hout hr
    have := hrt32 r hr
    omega
  all_goals omega

end Fv256.Arm64.FormatFast
