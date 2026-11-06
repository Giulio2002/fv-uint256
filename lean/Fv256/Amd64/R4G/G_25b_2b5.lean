import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_25b_2b5 (s : State) (x25brax x25brdx x25brbx x25brsi x25brdi x25br8 x25br9 x25br10 x25br11 x25br12 x25br13 x25br15 x25bm0 x25bm8 x25bm10 x25bm18 x25bm40 x25bm60 x25bm68 x25bm70 x25bm78 x25bm88 x25bm90 x25bm98 x25bma0 x25bma8 x25bmb0 x25bmb8 x25bmc0 x25bmc8 x25bmd0 x25bmd8 x25bm128 : Nat) (S' : State) : Prop :=
  ∃ x2b5rcx x2b5rbx x2b5r11 x2b5r13 x2b5r15, L2b5 s S' x25brax x2b5rcx x25brdx x2b5rbx x25brsi x25brdi x25br8 x25br9 x25br10 x2b5r11 x2b5r13 x2b5r15 x25bm0 x25bm8 x25bm10 x25bm18 x25bm60 x25bm68 x25bm70 x25bm88 x25bm90 x25bm98 x25bma0 x25bma8 x25bm128 ∧ x2b5rcx = (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2b5rbx = (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2b5r11 = (x25br11 + (x25bmd8 + x25brbx)) % 18446744073709551616 ∧ x2b5r13 = ((x25bm40 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb8 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x2b5r15 = (x25bmb8 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_25b_2b5 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x25b)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x25brax x25brdx x25brbx x25brsi x25brdi x25br8 x25br9 x25br10 x25br11 x25br12 x25br13 x25br15 x25bm0 x25bm8 x25bm10 x25bm18 x25bm40 x25bm60 x25bm68 x25bm70 x25bm78 x25bm88 x25bm90 x25bm98 x25bma0 x25bma8 x25bmb0 x25bmb8 x25bmc0 x25bmc8 x25bmd0 x25bmd8 x25bm128 : Nat) (hL : L25b s S x25brax x25brdx x25brbx x25brsi x25brdi x25br8 x25br9 x25br10 x25br11 x25br12 x25br13 x25br15 x25bm0 x25bm8 x25bm10 x25bm18 x25bm40 x25bm60 x25bm68 x25bm70 x25bm78 x25bm88 x25bm90 x25bm98 x25bma0 x25bma8 x25bmb0 x25bmb8 x25bmc0 x25bmc8 x25bmd0 x25bmd8 x25bm128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x2b5)) S (P_25b_2b5 s  x25brax x25brdx x25brbx x25brsi x25brdi x25br8 x25br9 x25br10 x25br11 x25br12 x25br13 x25br15 x25bm0 x25bm8 x25bm10 x25bm18 x25bm40 x25bm60 x25bm68 x25bm70 x25bm78 x25bm88 x25bm90 x25bm98 x25bma0 x25bma8 x25bmb0 x25bmb8 x25bmc0 x25bmc8 x25bmd0 x25bmd8 x25bm128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x25brax, hB_x25brax, hE_x25brdx, hB_x25brdx, hE_x25brbx, hB_x25brbx, hE_x25brsi, hB_x25brsi, hE_x25brdi, hB_x25brdi, hE_x25br8, hB_x25br8, hE_x25br9, hB_x25br9, hE_x25br10, hB_x25br10, hE_x25br11, hB_x25br11, hE_x25br12, hB_x25br12, hE_x25br13, hB_x25br13, hE_x25br15, hB_x25br15, hE_x25bm0, hB_x25bm0, hE_x25bm8, hB_x25bm8, hE_x25bm10, hB_x25bm10, hE_x25bm18, hB_x25bm18, hE_x25bm40, hB_x25bm40, hE_x25bm60, hB_x25bm60, hE_x25bm68, hB_x25bm68, hE_x25bm70, hB_x25bm70, hE_x25bm78, hB_x25bm78, hE_x25bm88, hB_x25bm88, hE_x25bm90, hB_x25bm90, hE_x25bm98, hB_x25bm98, hE_x25bma0, hB_x25bma0, hE_x25bma8, hB_x25bma8, hE_x25bmb0, hB_x25bmb0, hE_x25bmb8, hB_x25bmb8, hE_x25bmc0, hB_x25bmc0, hE_x25bmc8, hB_x25bmc8, hE_x25bmd0, hB_x25bmd0, hE_x25bmd8, hB_x25bmd8, hE_x25bm128, hB_x25bm128⟩ := hL
  janus64_run [Util.readLE_32, hE_x25brax, hE_x25brdx, hE_x25brbx, hE_x25brsi, hE_x25brdi, hE_x25br8, hE_x25br9, hE_x25br10, hE_x25br11, hE_x25br12, hE_x25br13, hE_x25br15, hE_x25bm0, hE_x25bm8, hE_x25bm10, hE_x25bm18, hE_x25bm40, hE_x25bm60, hE_x25bm68, hE_x25bm70, hE_x25bm78, hE_x25bm88, hE_x25bm90, hE_x25bm98, hE_x25bma0, hE_x25bma8, hE_x25bmb0, hE_x25bmb8, hE_x25bmc0, hE_x25bmc8, hE_x25bmd0, hE_x25bmd8, hE_x25bm128, hsp4, Nat.mod_eq_of_lt hB_x25brax, Nat.mod_eq_of_lt hB_x25brdx, Nat.mod_eq_of_lt hB_x25brbx, Nat.mod_eq_of_lt hB_x25brsi, Nat.mod_eq_of_lt hB_x25brdi, Nat.mod_eq_of_lt hB_x25br8, Nat.mod_eq_of_lt hB_x25br9, Nat.mod_eq_of_lt hB_x25br10, Nat.mod_eq_of_lt hB_x25br11, Nat.mod_eq_of_lt hB_x25br12, Nat.mod_eq_of_lt hB_x25br13, Nat.mod_eq_of_lt hB_x25br15, Nat.mod_eq_of_lt hB_x25bm0, Nat.mod_eq_of_lt hB_x25bm8, Nat.mod_eq_of_lt hB_x25bm10, Nat.mod_eq_of_lt hB_x25bm18, Nat.mod_eq_of_lt hB_x25bm40, Nat.mod_eq_of_lt hB_x25bm60, Nat.mod_eq_of_lt hB_x25bm68, Nat.mod_eq_of_lt hB_x25bm70, Nat.mod_eq_of_lt hB_x25bm78, Nat.mod_eq_of_lt hB_x25bm88, Nat.mod_eq_of_lt hB_x25bm90, Nat.mod_eq_of_lt hB_x25bm98, Nat.mod_eq_of_lt hB_x25bma0, Nat.mod_eq_of_lt hB_x25bma8, Nat.mod_eq_of_lt hB_x25bmb0, Nat.mod_eq_of_lt hB_x25bmb8, Nat.mod_eq_of_lt hB_x25bmc0, Nat.mod_eq_of_lt hB_x25bmc8, Nat.mod_eq_of_lt hB_x25bmd0, Nat.mod_eq_of_lt hB_x25bmd8, Nat.mod_eq_of_lt hB_x25bm128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_25b_2b5
  refine ⟨(x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x25br11 + (x25bmd8 + x25brbx)) % 18446744073709551616, ((x25bm40 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb8 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x25bmb8 + (x25bmc0 + x25br13 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bmb0 + (x25bmd0 + x25br12 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + (x25bm78 + (x25bmc8 + x25br15 + (x25bmd8 + x25brbx) / 18446744073709551616) % 18446744073709551616 + (x25br11 + (x25bmd8 + x25brbx) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L2b5
    and_intros
    · first | exact hE_x25brax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25brax)
    · exact hB_x25brax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x25brdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25brdx)
    · exact hB_x25brdx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x25brsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25brsi)
    · exact hB_x25brsi
    · first | exact hE_x25brdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25brdi)
    · exact hB_x25brdi
    · first | exact hE_x25br8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25br8)
    · exact hB_x25br8
    · first | exact hE_x25br9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25br9)
    · exact hB_x25br9
    · first | exact hE_x25br10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x25br10)
    · exact hB_x25br10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm0
    · exact hB_x25bm0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm8
    · exact hB_x25bm8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm10
    · exact hB_x25bm10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm18
    · exact hB_x25bm18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm60
    · exact hB_x25bm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm68
    · exact hB_x25bm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm70
    · exact hB_x25bm70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm88
    · exact hB_x25bm88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm90
    · exact hB_x25bm90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm98
    · exact hB_x25bm98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bma0
    · exact hB_x25bma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bma8
    · exact hB_x25bma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x25bm128
    · exact hB_x25bm128
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
