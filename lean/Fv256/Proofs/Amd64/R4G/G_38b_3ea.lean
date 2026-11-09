import Fv256.Proofs.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_38b_3ea (s : State) (x38brcx x38brbx x38brsi x38brdi x38br8 x38br9 x38br10 x38br11 x38br12 x38br13 x38br15 x38bm0 x38bm8 x38bm10 x38bm18 x38bm20 x38bm28 x38bm30 x38bm60 x38bm68 x38bm88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x38bm128 : Nat) (S' : State) : Prop :=
  ∃ x3earax x3earcx x3eardx x3earbx x3earsi x3ear8 x3eamc8 x3eamd0 x3eamd8 x3eame0, L3ea s S' x3earax x3earcx x3eardx x3earbx x3earsi x38brdi x3ear8 x38br9 x38br11 x38br12 x38br13 x38br15 x38bm0 x38bm8 x38bm10 x38bm18 x38bm20 x38bm28 x38bm30 x38bm60 x38bm68 x38bm88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x38bm128 ∧ x3earax = (x38bm60 * x38br10) % 18446744073709551616 ∧ x3earcx = (x38bm60 * x38brcx) % 18446744073709551616 ∧ x3eardx = (x38bm60 * x38br10 / 18446744073709551616) % 18446744073709551616 ∧ x3earbx = (x38bm60 * x38brbx) % 18446744073709551616 ∧ x3earsi = (x38bm60 * x38brsi) % 18446744073709551616 ∧ x3ear8 = (x38bm60 * x38br8) % 18446744073709551616 ∧ x3eamc8 = (x38bm60 * x38brsi / 18446744073709551616) % 18446744073709551616 ∧ x3eamd0 = (x38bm60 * x38brcx / 18446744073709551616) % 18446744073709551616 ∧ x3eamd8 = (x38bm60 * x38brbx / 18446744073709551616) % 18446744073709551616 ∧ x3eame0 = (x38bm68 * x38br10) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_38b_3ea (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x38b)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x38brcx x38brbx x38brsi x38brdi x38br8 x38br9 x38br10 x38br11 x38br12 x38br13 x38br15 x38bm0 x38bm8 x38bm10 x38bm18 x38bm20 x38bm28 x38bm30 x38bm60 x38bm68 x38bm88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x38bm128 : Nat) (hL : L38b s S x38brcx x38brbx x38brsi x38brdi x38br8 x38br9 x38br10 x38br11 x38br12 x38br13 x38br15 x38bm0 x38bm8 x38bm10 x38bm18 x38bm20 x38bm28 x38bm30 x38bm60 x38bm68 x38bm88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x38bm128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x3ea)) S (P_38b_3ea s  x38brcx x38brbx x38brsi x38brdi x38br8 x38br9 x38br10 x38br11 x38br12 x38br13 x38br15 x38bm0 x38bm8 x38bm10 x38bm18 x38bm20 x38bm28 x38bm30 x38bm60 x38bm68 x38bm88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x38bm128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x38brcx, hB_x38brcx, hE_x38brbx, hB_x38brbx, hE_x38brsi, hB_x38brsi, hE_x38brdi, hB_x38brdi, hE_x38br8, hB_x38br8, hE_x38br9, hB_x38br9, hE_x38br10, hB_x38br10, hE_x38br11, hB_x38br11, hE_x38br12, hB_x38br12, hE_x38br13, hB_x38br13, hE_x38br15, hB_x38br15, hE_x38bm0, hB_x38bm0, hE_x38bm8, hB_x38bm8, hE_x38bm10, hB_x38bm10, hE_x38bm18, hB_x38bm18, hE_x38bm20, hB_x38bm20, hE_x38bm28, hB_x38bm28, hE_x38bm30, hB_x38bm30, hE_x38bm60, hB_x38bm60, hE_x38bm68, hB_x38bm68, hE_x38bm88, hB_x38bm88, hE_x38bme8, hB_x38bme8, hE_x38bmf0, hB_x38bmf0, hE_x38bmf8, hB_x38bmf8, hE_x38bm100, hB_x38bm100, hE_x38bm108, hB_x38bm108, hE_x38bm110, hB_x38bm110, hE_x38bm128, hB_x38bm128⟩ := hL
  janus64_run [Util.readLE_32, hE_x38brcx, hE_x38brbx, hE_x38brsi, hE_x38brdi, hE_x38br8, hE_x38br9, hE_x38br10, hE_x38br11, hE_x38br12, hE_x38br13, hE_x38br15, hE_x38bm0, hE_x38bm8, hE_x38bm10, hE_x38bm18, hE_x38bm20, hE_x38bm28, hE_x38bm30, hE_x38bm60, hE_x38bm68, hE_x38bm88, hE_x38bme8, hE_x38bmf0, hE_x38bmf8, hE_x38bm100, hE_x38bm108, hE_x38bm110, hE_x38bm128, hsp4, Nat.mod_eq_of_lt hB_x38brcx, Nat.mod_eq_of_lt hB_x38brbx, Nat.mod_eq_of_lt hB_x38brsi, Nat.mod_eq_of_lt hB_x38brdi, Nat.mod_eq_of_lt hB_x38br8, Nat.mod_eq_of_lt hB_x38br9, Nat.mod_eq_of_lt hB_x38br10, Nat.mod_eq_of_lt hB_x38br11, Nat.mod_eq_of_lt hB_x38br12, Nat.mod_eq_of_lt hB_x38br13, Nat.mod_eq_of_lt hB_x38br15, Nat.mod_eq_of_lt hB_x38bm0, Nat.mod_eq_of_lt hB_x38bm8, Nat.mod_eq_of_lt hB_x38bm10, Nat.mod_eq_of_lt hB_x38bm18, Nat.mod_eq_of_lt hB_x38bm20, Nat.mod_eq_of_lt hB_x38bm28, Nat.mod_eq_of_lt hB_x38bm30, Nat.mod_eq_of_lt hB_x38bm60, Nat.mod_eq_of_lt hB_x38bm68, Nat.mod_eq_of_lt hB_x38bm88, Nat.mod_eq_of_lt hB_x38bme8, Nat.mod_eq_of_lt hB_x38bmf0, Nat.mod_eq_of_lt hB_x38bmf8, Nat.mod_eq_of_lt hB_x38bm100, Nat.mod_eq_of_lt hB_x38bm108, Nat.mod_eq_of_lt hB_x38bm110, Nat.mod_eq_of_lt hB_x38bm128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_38b_3ea
  refine ⟨(x38bm60 * x38br10) % 18446744073709551616, (x38bm60 * x38brcx) % 18446744073709551616, (x38bm60 * x38br10 / 18446744073709551616) % 18446744073709551616, (x38bm60 * x38brbx) % 18446744073709551616, (x38bm60 * x38brsi) % 18446744073709551616, (x38bm60 * x38br8) % 18446744073709551616, (x38bm60 * x38brsi / 18446744073709551616) % 18446744073709551616, (x38bm60 * x38brcx / 18446744073709551616) % 18446744073709551616, (x38bm60 * x38brbx / 18446744073709551616) % 18446744073709551616, (x38bm68 * x38br10) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L3ea
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x38brdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38brdi)
    · exact hB_x38brdi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x38br9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38br9)
    · exact hB_x38br9
    · first | exact hE_x38br11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38br11)
    · exact hB_x38br11
    · first | exact hE_x38br12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38br12)
    · exact hB_x38br12
    · first | exact hE_x38br13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38br13)
    · exact hB_x38br13
    · first | exact hE_x38br15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x38br15)
    · exact hB_x38br15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm0
    · exact hB_x38bm0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm8
    · exact hB_x38bm8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm10
    · exact hB_x38bm10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm18
    · exact hB_x38bm18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm20
    · exact hB_x38bm20
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm28
    · exact hB_x38bm28
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm30
    · exact hB_x38bm30
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm60
    · exact hB_x38bm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm68
    · exact hB_x38bm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm88
    · exact hB_x38bm88
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bme8
    · exact hB_x38bme8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bmf0
    · exact hB_x38bmf0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bmf8
    · exact hB_x38bmf8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm100
    · exact hB_x38bm100
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm108
    · exact hB_x38bm108
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm110
    · exact hB_x38bm110
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x38bm128
    · exact hB_x38bm128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
