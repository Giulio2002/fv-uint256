import Extracted
import Fv256.Proofs.Amd64.FormatNil

/-! the `"<nil>"` literal and its header are extracted data (n10 extractor): their facts follow from `DataLoaded` -/

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Fv256.Amd64.FormatNil

namespace Fv256.Amd64.FormatNil

theorem nil_rodata {m : Memory} (h : Extracted.program.DataLoaded m) :
    m.readLE hdrA 8 = litA ∧ m.readLE (hdrA + 8) 8 = 5 ∧ StrOut m litA 5 Fv256.FormatSpec.nilText := by
  have hdr : hdrA = 0x4f1190 := rfl
  have lit : litA = 0x4e5c16 := by decide
  have e1 : m.readLE hdrA 8 = dataReadD Extracted.program hdrA 8 :=
    readLE_dataReadD h _ _ (by rw [hdr]; decide +kernel)
  have e2 : m.readLE (hdrA + 8) 8 = dataReadD Extracted.program (hdrA + 8) 8 :=
    readLE_dataReadD h _ _ (by rw [hdr]; decide +kernel)
  have e3 : m.readLE litA 5 = dataReadD Extracted.program litA 5 :=
    readLE_dataReadD h _ _ (by rw [lit]; decide +kernel)
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hdr, lit]; decide +kernel
  · rw [e2, hdr]; decide +kernel
  · have hk : 4 < Extracted.program.data.length := by decide +kernel
    have hacc : m.accessible Extracted.data4.base Extracted.data4.bytes.length false = true := accessible_of_dataLoaded h 4 hk
    have hb : ∀ (i : Nat) (hi : i < Extracted.data4.bytes.length), (m.bytes (Extracted.data4.base + i)).toNat = Extracted.data4.bytes[i] :=
      (h _ (List.getElem_mem hk)).2
    have b0 := hb 0 (by decide +kernel)
    have b1 := hb 1 (by decide +kernel)
    have b2 := hb 2 (by decide +kernel)
    have b3 := hb 3 (by decide +kernel)
    have b4 := hb 4 (by decide +kernel)
    have hbase : Extracted.data4.base = litA := by rw [lit]; decide +kernel
    have hlen : Extracted.data4.bytes.length = 5 := by decide +kernel
    rw [hbase, hlen] at hacc
    rw [hbase] at b0 b1 b2 b3 b4
    simp only [Nat.add_zero] at b0
    refine ⟨rfl, by rw [lit]; decide, fun _ => hacc, ?_⟩
    simp only [Janus.Spec.strBytes, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil, List.nil_append]
    have c0 : (Extracted.data4.bytes[0]'(by decide +kernel)) = 60 := by decide +kernel
    have c1 : (Extracted.data4.bytes[1]'(by decide +kernel)) = 110 := by decide +kernel
    have c2 : (Extracted.data4.bytes[2]'(by decide +kernel)) = 105 := by decide +kernel
    have c3 : (Extracted.data4.bytes[3]'(by decide +kernel)) = 108 := by decide +kernel
    have c4 : (Extracted.data4.bytes[4]'(by decide +kernel)) = 62 := by decide +kernel
    rw [c0] at b0; rw [c1] at b1; rw [c2] at b2; rw [c3] at b3; rw [c4] at b4
    simp only [Fv256.FormatSpec.nilText, Nat.add_zero] 
    simp only [Nat.add_zero, List.singleton_append, List.cons_append, List.nil_append]
    rw [b0, b1, b2, b3, b4]

end Fv256.Amd64.FormatNil
