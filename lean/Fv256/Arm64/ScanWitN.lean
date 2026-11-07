import Extracted
import Fv256.Arm64.ScanWitC

/-! # Witness for `Scan` (arm64), part N: the string without an exponent -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.WitModel Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.Scan.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy

def pSV2 : BitVec 64 := BitVec.ofNat 64 str2W
def nSV2 : BitVec 64 := BitVec.ofNat 64 strBs2.length
def dwS2 : BitVec 64 := BitVec.ofNat 64 hdr2W

theorem hdrP_N : hdrP (st twS dwS2) dwS2 = pSV2 := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrP pSV2; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE hdr2W 8) % 2 ^ 64 = str2W % 2 ^ 64
  have : mem0.readLE hdr2W 8 = str2W := by decide
  rw [this]

theorem hdrN_N : hdrN (st twS dwS2) dwS2 = nSV2 := by
  apply BitVec.eq_of_toNat_eq
  unfold hdrN nSV2; simp only [BitVec.toNat_ofNat]
  show (mem0.readLE (hdr2W + 8) 8) % 2 ^ 64 = strBs2.length % 2 ^ 64
  have : mem0.readLE (hdr2W + 8) 8 = strBs2.length := by decide
  rw [this]

theorem chunkN : ChunkAll cfg R (R3 TW) [] 0x400 pSV2.toNat nSV2.toNat loW hiW mem0 := by
  intro sp sl h1 h2 h3 h4
  have e1 : pSV2.toNat = str2W := by decide
  have e2 : nSV2.toNat = strBs2.length := by decide
  have e3 : strBs2.length = 13 := by decide
  simp only [e1, e2, e3, str2W] at h1 h2
  have hsp : (BitVec.ofNat 64 sp).toNat = sp := Nat.mod_eq_of_lt (by omega)
  have hsl : (BitVec.ofNat 64 sl).toNat = sl := Nat.mod_eq_of_lt (by omega)
  have hacc : mem0.accessible str2W 13 false = true := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hsl]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, sl, h3, h4, rfl⟩)))
  · intro q; simp only [hsl, hsp]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, sp, sl, h3, h4, rfl⟩))))
  · simp only [hsl]; exact Nat.le_trans (chunk_bs sl h4) (Nat.le_refl _)
  · simp only [hsp, hsl]; exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by simp only [str2W]; omega) (by simp only [str2W]; omega)
  · simp only [hsp, hsl]; omega
  · simp only [hsp, hsl]; simp only [loW, hiW]; omega
  · left; simp only [hsp, hsl, rt_eq]; apply outside_of_decide
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [HEAP, HEND, HSIZE, BUMP, WBUF] <;> omega
  · simp only [hsp, hsl]; simp only [R3_priv]; apply outside_of_decide
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr; simp only [TW]; omega


theorem top0N : TopPre0 cfg R (R3 TW) TW 0x400 [] loW hiW zV pSV2 nSV2 (viewS (st twS dwS2) pSV2 nSV2) := by
  have hm := maxdig0
  have hc := chunkN
  unfold TopPre0
  refine ⟨by simp [viewS, setReg_apply, st], by simp [viewS, setReg_apply], by simp [viewS, setReg_apply],
    mod0, env0 twS dwS2, by decide, by decide, mult0, by decide, ?_, by decide, ?_, ?_, hm, by decide, ?_,
    ⟨by decide, by decide⟩, by decide, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, hc⟩
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R3_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide


theorem pageN : Fv256.IndexByte.PageReadable mem0 pSV2.toNat nSV2.toNat := by
  unfold Fv256.IndexByte.PageReadable
  right
  exact ⟨by decide, by decide⟩

theorem preN : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
    (Extracted.program.contractAddr "runtime.slicebytetostring") Extracted.dataAddr.«runtime.staticuint64s»
    Extracted.dataAddr.«type:errors.errorString#8e8100b7» R (R3 TW) TW 0x400 [] loW hiW zV twS dwS2 (st twS dwS2) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := pre_common twS dwS2
  refine ⟨a, b, c, d, e, f, g, h, Or.inr (Or.inl ⟨by decide, ⟨by decide, by decide⟩, Or.inr (by decide), ?_, initDone0, ?_⟩)⟩
  · rw [hdrP_N, hdrN_N]; exact top0N
  · rw [hdrP_N, hdrN_N]; exact pageN



end Fv256.Arm64.Scan.Witness
