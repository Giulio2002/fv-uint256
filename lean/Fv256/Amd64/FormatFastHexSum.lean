import Extracted
import Fv256.FormatFastDefs
import Fv256.Amd64.FM.Hex

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

abbrev nmHex : String := "github.com/holiman/uint256.(*Int).Hex"
abbrev P0H (impl : List Amd64.Segment) : Amd64.Program := (Extracted.program.onlySegments [nmHex]).link impl

theorem hx_Hex (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) :
    (P0H impl).fetch (P0H impl).exitAddr = none := by
  cases hf : (P0H impl).fetch (P0H impl).exitAddr with
  | none => rfl
  | some w =>
    exfalso
    have e : (P0H impl).exitAddr = Extracted.program.exitAddr := rfl
    have := (codeIn_restrict_of_apart64 hI [nmHex]) _ _ hf
    obtain ⟨-, -, hne⟩ := this
    exact hne rfl

/-- `Hex` as a summary in the whole program (`Ensures.toSummaryIn`, ToBig style) -/
def hex_summary (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (hI : ImplApart Extracted.program impl)
    (hc : RtContract64 (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :=
  Ensures.toSummaryIn (Fv256.Amd64.FM.Hex.correctness impl rt H z hc) (hx_Hex impl hI) (by show 1 ≤ 9; decide)
    (codeIn_restrict_of_apart64 hI [nmHex])

end Fv256.Amd64.FormatFast
