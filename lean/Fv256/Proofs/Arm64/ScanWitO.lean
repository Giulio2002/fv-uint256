import Extracted
import Fv256.Proofs.Arm64.ScanWitC

/-! # Witness for `Scan` (arm64), part O: the nil, `[]byte` and unsupported-type call states -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.WitModel Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.Scan.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy

def twB : BitVec 64 := BitVec.ofNat 64 tyB
def twU : BitVec 64 := BitVec.ofNat 64 tyU
def pBV : BitVec 64 := BitVec.ofNat 64 bufW
def nBV : BitVec 64 := 48#64
def dwSl : BitVec 64 := BitVec.ofNat 64 slW

theorem preNil : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
    (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV 0#64 0#64 (st 0#64 0#64) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := pre_common 0#64 0#64
  refine ⟨a, b, c, d, e, f, g, h, Or.inl ⟨rfl, ⟨by decide, by decide⟩, Or.inr (by decide), by decide⟩⟩

theorem preOther : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
    (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twU 0#64 (st twU 0#64) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := pre_common twU 0#64
  refine ⟨a, b, c, d, e, f, g, h, Or.inr (Or.inr (Or.inr ⟨by decide, by decide, by decide, by decide, Or.inl (by decide),
    mod0, env0 twU 0#64, Or.inl ⟨rfl, Or.inr rfl⟩, by decide, ?_, Or.inr (by decide), ?_⟩))⟩
  · rw [rt_eq]; apply outside_of_decide; decide
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide


theorem hdrP_B : hdrP (st twB dwSl) dwSl = pBV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrP pBV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE slW 8) % 2 ^ 64 = bufW % 2 ^ 64
  have : mem0.readLE slW 8 = bufW := by decide
  rw [this]

theorem hdrN_B : hdrN (st twB dwSl) dwSl = nBV := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrN nBV; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE (slW + 8) 8) % 2 ^ 64 = 48 % 2 ^ 64
  have : mem0.readLE (slW + 8) 8 = 48 := by decide
  rw [this]

theorem preB0 : PreB cfg (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    R (R3 TW) TW 0x400 [] loW hiW zV pBV nBV (st twB dwSl) := by
  have hm := maxdig0
  unfold PreB
  refine ⟨mod0, env0 twB dwSl, ?_, by decide, ?_, ?_, ?_, ?_, mult0, ?_, ?_, by decide, ?_, ?_, by decide, ?_, ?_,
    initDone0, by decide, ?_, ?_, hm, ⟨by decide, by decide⟩, by decide, ?_, ?_, ?_, ?_, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by decide, _, pBV.toNat, rfl⟩))))
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rw [rt_eq]
    rcases hk with rfl | rfl | rfl | rfl <;> (apply outside_of_decide; decide)
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide
  · exact Or.inr (by decide)
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro sl h1 h2 h3
    have hn : nBV.toNat = 48 := by decide
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h1, h2, rfl⟩))),
      fun q p => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, p, sl, h1, h2, rfl⟩)))), ?_⟩
    have : blockSize sl true + blockSize 48 false ≤ 0x400 - 48 := by
      have h19 : ∀ sl, sl ≤ 19 → blockSize sl true + blockSize 48 false ≤ 0x400 - 48 := by decide
      exact h19 sl h2
    have h48 : roundupsize 48 true = 48 := by decide
    rw [hn, h48]; exact this


theorem pagesB0 : PagesB R Extracted.dataAddr.«runtime.staticuint64s» loW hiW mem0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Fv256.IndexByte.PageReadable; right; exact ⟨by decide, by decide⟩
  · intro r hr
    rw [rt_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    unfold Fv256.IndexByte.PageReadable
    rcases hr with rfl | rfl | rfl <;> (right; exact ⟨by decide, by decide⟩)
  · unfold Fv256.IndexByte.PageReadable; right; exact ⟨by decide, by decide⟩

theorem preByt : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
    (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twB dwSl (st twB dwSl) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := pre_common twB dwSl
  refine ⟨a, b, c, d, e, f, g, h, Or.inr (Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, Or.inr (by decide), ?_, pagesB0⟩))⟩
  rw [hdrP_B, hdrN_B]; exact preB0

end Fv256.Arm64.Scan.Witness
