import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_46b_47f (s : State) (x46brax x46brcx x46brdx x46brbx x46brsi x46brdi x46br9 x46br11 x46br12 x46br13 x46bm0 x46bm8 x46bm10 x46bm18 x46bm60 x46bm68 x46bm88 x46bmc8 x46bm128 : Nat) (S' : State) : Prop :=
  ∃ x47frax x47frsi x47fr8 x47fr11, L47f s S' x47frax x46brbx x47frsi x46brdi x47fr8 x46br9 x47fr11 x46br12 x46bm0 x46bm8 x46bm10 x46bm18 x46bm60 x46bm68 x46bm88 x46bm128 ∧ x47frax = (x46brax + x46br9 + (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x47frsi = (x46brsi + x46br13) % 18446744073709551616 ∧ x47fr8 = (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) % 18446744073709551616 ∧ x47fr11 = (x46br11 + x46brdx + (x46brax + x46br9 + (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_46b_47f (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x46b)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x46brax x46brcx x46brdx x46brbx x46brsi x46brdi x46br9 x46br11 x46br12 x46br13 x46bm0 x46bm8 x46bm10 x46bm18 x46bm60 x46bm68 x46bm88 x46bmc8 x46bm128 : Nat) (hL : L46b s S x46brax x46brcx x46brdx x46brbx x46brsi x46brdi x46br9 x46br11 x46br12 x46br13 x46bm0 x46bm8 x46bm10 x46bm18 x46bm60 x46bm68 x46bm88 x46bmc8 x46bm128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x47f)) S (P_46b_47f s  x46brax x46brcx x46brdx x46brbx x46brsi x46brdi x46br9 x46br11 x46br12 x46br13 x46bm0 x46bm8 x46bm10 x46bm18 x46bm60 x46bm68 x46bm88 x46bmc8 x46bm128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x46brax, hB_x46brax, hE_x46brcx, hB_x46brcx, hE_x46brdx, hB_x46brdx, hE_x46brbx, hB_x46brbx, hE_x46brsi, hB_x46brsi, hE_x46brdi, hB_x46brdi, hE_x46br9, hB_x46br9, hE_x46br11, hB_x46br11, hE_x46br12, hB_x46br12, hE_x46br13, hB_x46br13, hE_x46bm0, hB_x46bm0, hE_x46bm8, hB_x46bm8, hE_x46bm10, hB_x46bm10, hE_x46bm18, hB_x46bm18, hE_x46bm60, hB_x46bm60, hE_x46bm68, hB_x46bm68, hE_x46bm88, hB_x46bm88, hE_x46bmc8, hB_x46bmc8, hE_x46bm128, hB_x46bm128⟩ := hL
  janus64_run [Util.readLE_32, hE_x46brax, hE_x46brcx, hE_x46brdx, hE_x46brbx, hE_x46brsi, hE_x46brdi, hE_x46br9, hE_x46br11, hE_x46br12, hE_x46br13, hE_x46bm0, hE_x46bm8, hE_x46bm10, hE_x46bm18, hE_x46bm60, hE_x46bm68, hE_x46bm88, hE_x46bmc8, hE_x46bm128, hsp4, Nat.mod_eq_of_lt hB_x46brax, Nat.mod_eq_of_lt hB_x46brcx, Nat.mod_eq_of_lt hB_x46brdx, Nat.mod_eq_of_lt hB_x46brbx, Nat.mod_eq_of_lt hB_x46brsi, Nat.mod_eq_of_lt hB_x46brdi, Nat.mod_eq_of_lt hB_x46br9, Nat.mod_eq_of_lt hB_x46br11, Nat.mod_eq_of_lt hB_x46br12, Nat.mod_eq_of_lt hB_x46br13, Nat.mod_eq_of_lt hB_x46bm0, Nat.mod_eq_of_lt hB_x46bm8, Nat.mod_eq_of_lt hB_x46bm10, Nat.mod_eq_of_lt hB_x46bm18, Nat.mod_eq_of_lt hB_x46bm60, Nat.mod_eq_of_lt hB_x46bm68, Nat.mod_eq_of_lt hB_x46bm88, Nat.mod_eq_of_lt hB_x46bmc8, Nat.mod_eq_of_lt hB_x46bm128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_46b_47f
  refine ⟨(x46brax + x46br9 + (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x46brsi + x46br13) % 18446744073709551616, (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) % 18446744073709551616, (x46br11 + x46brdx + (x46brax + x46br9 + (x46bmc8 + x46brcx + (x46brsi + x46br13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L47f
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x46brbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x46brbx)
    · exact hB_x46brbx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x46brdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x46brdi)
    · exact hB_x46brdi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x46br9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x46br9)
    · exact hB_x46br9
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x46br12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x46br12)
    · exact hB_x46br12
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm0
    · exact hB_x46bm0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm8
    · exact hB_x46bm8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm10
    · exact hB_x46bm10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm18
    · exact hB_x46bm18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm60
    · exact hB_x46bm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm68
    · exact hB_x46bm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm88
    · exact hB_x46bm88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x46bm128
    · exact hB_x46bm128
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
