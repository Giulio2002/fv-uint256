import Extracted
import Fv256.FormatFastDefsA64
import Fv256.Arm64.FM.Hex

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Janus.Contracts.EqHashModel

namespace Fv256.Arm64.FormatFast

abbrev nmHex : String := "github.com/holiman/uint256.(*Int).Hex"
abbrev P0H (impl : List Segment) : Program := (Extracted.program.onlySegments [nmHex]).link impl

theorem fetchIn_none_of (segs : List Segment) (pc : Nat)
    (h : ∀ seg ∈ segs, ∀ i < seg.words.length, pc ≠ seg.base + 4 * i) : Program.fetchIn segs pc = none := by
  cases hf : Program.fetchIn segs pc with
  | none => rfl
  | some w =>
    obtain ⟨seg, hm, i, hi, hpc⟩ := Program.fetchIn_index hf
    exact absurd hpc (h seg hm i hi)

theorem hc_Hex (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    CodeIn (P0H impl) (Extracted.program.link impl) :=
  codeIn_restrict Extracted.program [nmHex] impl hI.1 hI.2

theorem hx_Hex (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    (P0H impl).fetch (P0H impl).exitAddr = none := by
  apply fetchIn_none_of
  intro seg hseg i hi
  have hm : seg ∈ Extracted.program.segments ++ impl := by
    rcases List.mem_append.1 hseg with h | h
    · exact List.mem_append_left _ (List.mem_filter.1 h).1
    · exact List.mem_append_right _ h
  exact fun h => (hI.2 seg hm i hi).2 h.symm

/-- `Hex` as a summary in the whole program (`Ensures.toSummaryIn`, ToBig style) -/
def hex_summary (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (hI : ImplApart Extracted.program impl)
    (hc : RtContract (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :=
  Ensures.toSummaryIn (Fv256.Arm64.FM.Hex.correctness impl rt H z hc) (hx_Hex impl hI) (hc_Hex impl hI)

end Fv256.Arm64.FormatFast
