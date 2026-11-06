import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_47f_4ac (s : State) (x47frax x47frbx x47frsi x47frdi x47fr8 x47fr9 x47fr11 x47fr12 x47fm0 x47fm8 x47fm10 x47fm18 x47fm60 x47fm68 x47fm88 x47fm128 : Nat) (S' : State) : Prop :=
  ∃ x4acrcx x4acrdx x4acrbx x4acrsi x4acr8 x4acr9, L4ac s S' x4acrcx x4acrdx x4acrbx x4acrsi x47frdi x4acr8 x4acr9 x47fr11 x47fr12 x47fm60 x47fm68 x47fm128 ∧ x4acrcx = (BitVec.ofNat 64 x47fm88 - BitVec.ofNat 64 x47frbx).toNat ∧ x4acrdx = (x47fm10 % 18446744073709551616 + 18446744073709551616 - x47frsi % 18446744073709551616 - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616)) % 18446744073709551616 ∧ x4acrbx = (x47fm8 % 18446744073709551616 + 18446744073709551616 - x47fr8 % 18446744073709551616 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616 ∧ x4acrsi = (x47fm18 % 18446744073709551616 + 18446744073709551616 - x47frax % 18446744073709551616 - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616 ∧ x4acr8 = (x47fm0 % 18446744073709551616 + 18446744073709551616 - x47fr11 % 18446744073709551616 - (1 - (x47fm18 + (18446744073709551616 - x47frax - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616 ∧ x4acr9 = (if x47fm0 < x47fr11 + (1 - (x47fm18 + (18446744073709551616 - x47frax - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616) then 18446744073709551615#64 else 0#64).toNat ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_47f_4ac (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x47f)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x47frax x47frbx x47frsi x47frdi x47fr8 x47fr9 x47fr11 x47fr12 x47fm0 x47fm8 x47fm10 x47fm18 x47fm60 x47fm68 x47fm88 x47fm128 : Nat) (hL : L47f s S x47frax x47frbx x47frsi x47frdi x47fr8 x47fr9 x47fr11 x47fr12 x47fm0 x47fm8 x47fm10 x47fm18 x47fm60 x47fm68 x47fm88 x47fm128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x4ac)) S (P_47f_4ac s  x47frax x47frbx x47frsi x47frdi x47fr8 x47fr9 x47fr11 x47fr12 x47fm0 x47fm8 x47fm10 x47fm18 x47fm60 x47fm68 x47fm88 x47fm128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x47frax, hB_x47frax, hE_x47frbx, hB_x47frbx, hE_x47frsi, hB_x47frsi, hE_x47frdi, hB_x47frdi, hE_x47fr8, hB_x47fr8, hE_x47fr9, hB_x47fr9, hE_x47fr11, hB_x47fr11, hE_x47fr12, hB_x47fr12, hE_x47fm0, hB_x47fm0, hE_x47fm8, hB_x47fm8, hE_x47fm10, hB_x47fm10, hE_x47fm18, hB_x47fm18, hE_x47fm60, hB_x47fm60, hE_x47fm68, hB_x47fm68, hE_x47fm88, hB_x47fm88, hE_x47fm128, hB_x47fm128⟩ := hL
  janus64_run [Util.readLE_32, hE_x47frax, hE_x47frbx, hE_x47frsi, hE_x47frdi, hE_x47fr8, hE_x47fr9, hE_x47fr11, hE_x47fr12, hE_x47fm0, hE_x47fm8, hE_x47fm10, hE_x47fm18, hE_x47fm60, hE_x47fm68, hE_x47fm88, hE_x47fm128, hsp4, Nat.mod_eq_of_lt hB_x47frax, Nat.mod_eq_of_lt hB_x47frbx, Nat.mod_eq_of_lt hB_x47frsi, Nat.mod_eq_of_lt hB_x47frdi, Nat.mod_eq_of_lt hB_x47fr8, Nat.mod_eq_of_lt hB_x47fr9, Nat.mod_eq_of_lt hB_x47fr11, Nat.mod_eq_of_lt hB_x47fr12, Nat.mod_eq_of_lt hB_x47fm0, Nat.mod_eq_of_lt hB_x47fm8, Nat.mod_eq_of_lt hB_x47fm10, Nat.mod_eq_of_lt hB_x47fm18, Nat.mod_eq_of_lt hB_x47fm60, Nat.mod_eq_of_lt hB_x47fm68, Nat.mod_eq_of_lt hB_x47fm88, Nat.mod_eq_of_lt hB_x47fm128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_47f_4ac
  refine ⟨(BitVec.ofNat 64 x47fm88 - BitVec.ofNat 64 x47frbx).toNat, (x47fm10 % 18446744073709551616 + 18446744073709551616 - x47frsi % 18446744073709551616 - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616)) % 18446744073709551616, (x47fm8 % 18446744073709551616 + 18446744073709551616 - x47fr8 % 18446744073709551616 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616, (x47fm18 % 18446744073709551616 + 18446744073709551616 - x47frax % 18446744073709551616 - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616, (x47fm0 % 18446744073709551616 + 18446744073709551616 - x47fr11 % 18446744073709551616 - (1 - (x47fm18 + (18446744073709551616 - x47frax - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616, (if x47fm0 < x47fr11 + (1 - (x47fm18 + (18446744073709551616 - x47frax - (1 - (x47fm8 + (18446744073709551616 - x47fr8 - (1 - (x47fm10 + (18446744073709551616 - x47frsi - (1 - (x47fm88 + (18446744073709551616 - x47frbx)) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616))) / 18446744073709551616) then 18446744073709551615#64 else 0#64).toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L4ac
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x47frdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x47frdi)
    · exact hB_x47frdi
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x47fr11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x47fr11)
    · exact hB_x47fr11
    · first | exact hE_x47fr12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x47fr12)
    · exact hB_x47fr12
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x47fm60
    · exact hB_x47fm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x47fm68
    · exact hB_x47fm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x47fm128
    · exact hB_x47fm128
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
