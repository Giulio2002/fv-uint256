import Extracted
import Fv256.MsaCommon
import Fv256.Arm64.MarshalSSZAppendG
import Fv256.Arm64.MsaBlk1
import Fv256.Arm64.MsaBlk2
import Fv256.Arm64.MsaBlk3

/-!
# `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` (arm64): the full spec

`dst = append(dst, z[0..3] little-endian)` as four 8-byte appends, each with its own capacity check and its own
`runtime.growslice(p, n, c, 8, uint8)` call. Result `(x0, len + 32, x2)` and a nil error (`x3 = x4 = 0`); the bytes
`[len, len + 32)` of the result are the little-endian encoding of `*z`, the first `len` bytes are the old ones, and:
if `len + 32 <= cap` the result is `(dp, len + 32, cap)` and only the 32 bytes (and the stack) change; otherwise the
result array is inside the runtime's ranges `R.rt` and the invariant holds again for a live set containing it.
Runtime assumptions: the `growslice` live contract, `DescOK` for the `uint8` descriptor, the runtime ready for the
requests the code makes (`Ready`) and the budget `4 * Kc len <= b`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa Fv256.Arm64.MarshalSSZAppendG

namespace Fv256.Arm64.MarshalSSZAppendMain

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (fun s => GuardOK s 4224 ∧ StackOK s 4232 40 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4232) 4272 ∧
        Outside (s.sp.toNat - 4232) 4272 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4232) 4272 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 dp.toNat cap.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
        (InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt) ∧
        Apart z.toNat 32 dp.toNat cap.toNat ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ dp.toNat + cap.toNat ≤ 2 ^ 48 ∧
        Apart dp.toNat cap.toNat (s.sp.toNat - 4232) 4272 ∧
        Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat)
      (fun s s' => AppendPost R s s' z dp.toNat len.toNat cap.toNat b L) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, ⟨hzp, hz48⟩, hzd, hout, hga, hgr, hgd, hinv, hLs, hzL, hzpd,
    hlc, hC, hPb, hdj, hdt, hdtd, hdesc, hroom, hgrow, hbud, hrdy⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x24]
  have hl0b : len.toNat < 2 ^ 40 := by omega
  have hl8 : (len + 8#64).toNat = len.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hl16 : (len + 8#64 + 8#64).toNat = len.toNat + 16 := by rw [BitVec.toNat_add, hl8]; simp; omega
  have hl24 : (len + 8#64 + 8#64 + 8#64).toNat = len.toNat + 24 := by rw [BitVec.toNat_add, hl16]; simp; omega
  refine blk0 impl R ret hret hgs s _ z dp.toNat len.toNat cap.toNat b b len dp cap L L _ hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc
    rfl (by omega) hl0b (by first | rfl | decide) 3 ?_
    (fun S1 pp1 cc1 b1 L1 hpc1 hI1 hb1 => blk1 impl R ret hret hgs s S1 z dp.toNat len.toNat cap.toNat b1 b (len + 8#64) pp1 cc1 L1 L _
      hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc1 2 hI1
      (fun S2 pp2 cc2 b2 L2 hpc2 hI2 hb2 => blk2 impl R ret hret hgs s S2 z dp.toNat len.toNat cap.toNat b2 b (len + 8#64 + 8#64) pp2 cc2 L2 L _
        hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc2 1 hI2
        (fun S3 pp3 cc3 b3 L3 hpc3 hI3 hb3 => blk3f impl R ret hret hgs s S3 z dp.toNat len.toNat cap.toNat b3 b (len + 8#64 + 8#64 + 8#64) pp3 cc3 L3 L
          hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc3 0 hI3)))
  have hret48 := hret.user
  have hstk : ∀ a n, (s.sp.toNat - 4232 ≤ a → a + n ≤ s.sp.toNat + 40 → Outside a n R.rt) :=
    fun a n h1 h2 => Outside.of_sub hout (by omega) (by omega)
  refine ⟨rfl, by simp [setReg, h_x0], by simp [setReg, h_x1], by simp [setReg, h_x3], by simp [setReg], by simp [setReg],
    by simp [setReg], by simp [setReg], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLs, hzL, hzpd, Nat.le_refl _, by omega, hlc, by omega, hPb, hdj,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; omega)
  · simp only []
    rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := z.isLt; omega)
  · simp only [Memory.accessible_writeLE]; exact hw
  · simp only []
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
  · intro hc
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only []
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
  · intro i hi
    simp only []
    unfold Disjoint at hzd
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · simp only []
    rw [view_writeLE_out (hstk _ _ (by omega) (by omega)), view_writeLE_out (hstk _ _ (by omega) (by omega)),
      view_writeLE_out (hstk _ _ (by omega) (by omega)), view_writeLE_out (hstk _ _ (by omega) (by omega))]
    exact hinv
  · intro h
    simp only [Memory.accessible_writeLE]; exact hroom h
  · intro h h0
    simp only [Memory.accessible_writeLE]; exact hgrow h h0
  · simpa using hbud
  · exact hrdy
  · intro i hi
    simp only []
    unfold Apart at hdj
    rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
      Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega)]
  · simp

end Fv256.Arm64.MarshalSSZAppendMain
