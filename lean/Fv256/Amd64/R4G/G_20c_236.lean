import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_20c_236 (s : State) (x20crax x20crcx x20crdx x20crsi x20crdi x20cr8 x20cr9 x20cr10 x20cr11 x20cr12 x20cr13 x20cm0 x20cm8 x20cm10 x20cm18 x20cm40 x20cm48 x20cm60 x20cm68 x20cm70 x20cm78 x20cm80 x20cm88 x20cm90 x20cm98 x20cma0 x20cma8 x20cmb0 x20cmb8 x20cmc0 x20cmc8 x20cmd0 x20cmd8 x20cme0 x20cme8 x20cmf0 x20cmf8 x20cm100 x20cm128 : Nat) (S' : State) : Prop :=
  ∃ x236rcx x236r12 x236r13 x236r15, L236 s S' x20crax x236rcx x20crdx x20crsi x20crdi x20cr8 x20cr9 x20cr10 x20cr11 x236r12 x236r13 x236r15 x20cm0 x20cm8 x20cm10 x20cm18 x20cm40 x20cm60 x20cm68 x20cm70 x20cm78 x20cm80 x20cm88 x20cm90 x20cm98 x20cma0 x20cma8 x20cmb0 x20cmb8 x20cmc0 x20cmc8 x20cmd0 x20cmd8 x20cme0 x20cme8 x20cm128 ∧ x236rcx = (x20cmf0 + x20cr13 + (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x236r12 = (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) % 18446744073709551616 ∧ x236r13 = (x20cm48 + (x20cmf0 + x20cr13 + (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x236r15 = (x20cmf8 + x20cr12) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_20c_236 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x20c)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x20crax x20crcx x20crdx x20crsi x20crdi x20cr8 x20cr9 x20cr10 x20cr11 x20cr12 x20cr13 x20cm0 x20cm8 x20cm10 x20cm18 x20cm40 x20cm48 x20cm60 x20cm68 x20cm70 x20cm78 x20cm80 x20cm88 x20cm90 x20cm98 x20cma0 x20cma8 x20cmb0 x20cmb8 x20cmc0 x20cmc8 x20cmd0 x20cmd8 x20cme0 x20cme8 x20cmf0 x20cmf8 x20cm100 x20cm128 : Nat) (hL : L20c s S x20crax x20crcx x20crdx x20crsi x20crdi x20cr8 x20cr9 x20cr10 x20cr11 x20cr12 x20cr13 x20cm0 x20cm8 x20cm10 x20cm18 x20cm40 x20cm48 x20cm60 x20cm68 x20cm70 x20cm78 x20cm80 x20cm88 x20cm90 x20cm98 x20cma0 x20cma8 x20cmb0 x20cmb8 x20cmc0 x20cmc8 x20cmd0 x20cmd8 x20cme0 x20cme8 x20cmf0 x20cmf8 x20cm100 x20cm128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x236)) S (P_20c_236 s  x20crax x20crcx x20crdx x20crsi x20crdi x20cr8 x20cr9 x20cr10 x20cr11 x20cr12 x20cr13 x20cm0 x20cm8 x20cm10 x20cm18 x20cm40 x20cm48 x20cm60 x20cm68 x20cm70 x20cm78 x20cm80 x20cm88 x20cm90 x20cm98 x20cma0 x20cma8 x20cmb0 x20cmb8 x20cmc0 x20cmc8 x20cmd0 x20cmd8 x20cme0 x20cme8 x20cmf0 x20cmf8 x20cm100 x20cm128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x20crax, hB_x20crax, hE_x20crcx, hB_x20crcx, hE_x20crdx, hB_x20crdx, hE_x20crsi, hB_x20crsi, hE_x20crdi, hB_x20crdi, hE_x20cr8, hB_x20cr8, hE_x20cr9, hB_x20cr9, hE_x20cr10, hB_x20cr10, hE_x20cr11, hB_x20cr11, hE_x20cr12, hB_x20cr12, hE_x20cr13, hB_x20cr13, hE_x20cm0, hB_x20cm0, hE_x20cm8, hB_x20cm8, hE_x20cm10, hB_x20cm10, hE_x20cm18, hB_x20cm18, hE_x20cm40, hB_x20cm40, hE_x20cm48, hB_x20cm48, hE_x20cm60, hB_x20cm60, hE_x20cm68, hB_x20cm68, hE_x20cm70, hB_x20cm70, hE_x20cm78, hB_x20cm78, hE_x20cm80, hB_x20cm80, hE_x20cm88, hB_x20cm88, hE_x20cm90, hB_x20cm90, hE_x20cm98, hB_x20cm98, hE_x20cma0, hB_x20cma0, hE_x20cma8, hB_x20cma8, hE_x20cmb0, hB_x20cmb0, hE_x20cmb8, hB_x20cmb8, hE_x20cmc0, hB_x20cmc0, hE_x20cmc8, hB_x20cmc8, hE_x20cmd0, hB_x20cmd0, hE_x20cmd8, hB_x20cmd8, hE_x20cme0, hB_x20cme0, hE_x20cme8, hB_x20cme8, hE_x20cmf0, hB_x20cmf0, hE_x20cmf8, hB_x20cmf8, hE_x20cm100, hB_x20cm100, hE_x20cm128, hB_x20cm128⟩ := hL
  janus64_run [Util.readLE_32, hE_x20crax, hE_x20crcx, hE_x20crdx, hE_x20crsi, hE_x20crdi, hE_x20cr8, hE_x20cr9, hE_x20cr10, hE_x20cr11, hE_x20cr12, hE_x20cr13, hE_x20cm0, hE_x20cm8, hE_x20cm10, hE_x20cm18, hE_x20cm40, hE_x20cm48, hE_x20cm60, hE_x20cm68, hE_x20cm70, hE_x20cm78, hE_x20cm80, hE_x20cm88, hE_x20cm90, hE_x20cm98, hE_x20cma0, hE_x20cma8, hE_x20cmb0, hE_x20cmb8, hE_x20cmc0, hE_x20cmc8, hE_x20cmd0, hE_x20cmd8, hE_x20cme0, hE_x20cme8, hE_x20cmf0, hE_x20cmf8, hE_x20cm100, hE_x20cm128, hsp4, Nat.mod_eq_of_lt hB_x20crax, Nat.mod_eq_of_lt hB_x20crcx, Nat.mod_eq_of_lt hB_x20crdx, Nat.mod_eq_of_lt hB_x20crsi, Nat.mod_eq_of_lt hB_x20crdi, Nat.mod_eq_of_lt hB_x20cr8, Nat.mod_eq_of_lt hB_x20cr9, Nat.mod_eq_of_lt hB_x20cr10, Nat.mod_eq_of_lt hB_x20cr11, Nat.mod_eq_of_lt hB_x20cr12, Nat.mod_eq_of_lt hB_x20cr13, Nat.mod_eq_of_lt hB_x20cm0, Nat.mod_eq_of_lt hB_x20cm8, Nat.mod_eq_of_lt hB_x20cm10, Nat.mod_eq_of_lt hB_x20cm18, Nat.mod_eq_of_lt hB_x20cm40, Nat.mod_eq_of_lt hB_x20cm48, Nat.mod_eq_of_lt hB_x20cm60, Nat.mod_eq_of_lt hB_x20cm68, Nat.mod_eq_of_lt hB_x20cm70, Nat.mod_eq_of_lt hB_x20cm78, Nat.mod_eq_of_lt hB_x20cm80, Nat.mod_eq_of_lt hB_x20cm88, Nat.mod_eq_of_lt hB_x20cm90, Nat.mod_eq_of_lt hB_x20cm98, Nat.mod_eq_of_lt hB_x20cma0, Nat.mod_eq_of_lt hB_x20cma8, Nat.mod_eq_of_lt hB_x20cmb0, Nat.mod_eq_of_lt hB_x20cmb8, Nat.mod_eq_of_lt hB_x20cmc0, Nat.mod_eq_of_lt hB_x20cmc8, Nat.mod_eq_of_lt hB_x20cmd0, Nat.mod_eq_of_lt hB_x20cmd8, Nat.mod_eq_of_lt hB_x20cme0, Nat.mod_eq_of_lt hB_x20cme8, Nat.mod_eq_of_lt hB_x20cmf0, Nat.mod_eq_of_lt hB_x20cmf8, Nat.mod_eq_of_lt hB_x20cm100, Nat.mod_eq_of_lt hB_x20cm128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_20c_236
  refine ⟨(x20cmf0 + x20cr13 + (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) % 18446744073709551616, (x20cm48 + (x20cmf0 + x20cr13 + (x20cm100 + x20crcx + (x20cmf8 + x20cr12) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x20cmf8 + x20cr12) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L236
    and_intros
    · first | exact hE_x20crax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20crax)
    · exact hB_x20crax
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x20crdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20crdx)
    · exact hB_x20crdx
    · first | exact hE_x20crsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20crsi)
    · exact hB_x20crsi
    · first | exact hE_x20crdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20crdi)
    · exact hB_x20crdi
    · first | exact hE_x20cr8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20cr8)
    · exact hB_x20cr8
    · first | exact hE_x20cr9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20cr9)
    · exact hB_x20cr9
    · first | exact hE_x20cr10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20cr10)
    · exact hB_x20cr10
    · first | exact hE_x20cr11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x20cr11)
    · exact hB_x20cr11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm0
    · exact hB_x20cm0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm8
    · exact hB_x20cm8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm10
    · exact hB_x20cm10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm18
    · exact hB_x20cm18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm40
    · exact hB_x20cm40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm60
    · exact hB_x20cm60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm68
    · exact hB_x20cm68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm70
    · exact hB_x20cm70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm78
    · exact hB_x20cm78
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm80
    · exact hB_x20cm80
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm88
    · exact hB_x20cm88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm90
    · exact hB_x20cm90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm98
    · exact hB_x20cm98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cma0
    · exact hB_x20cma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cma8
    · exact hB_x20cma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmb0
    · exact hB_x20cmb0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmb8
    · exact hB_x20cmb8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmc0
    · exact hB_x20cmc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmc8
    · exact hB_x20cmc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmd0
    · exact hB_x20cmd0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cmd8
    · exact hB_x20cmd8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cme0
    · exact hB_x20cme0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cme8
    · exact hB_x20cme8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x20cm128
    · exact hB_x20cm128
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
