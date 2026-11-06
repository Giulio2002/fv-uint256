import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_3ea_429 (s : State) (x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x3ear9 x3ear11 x3ear12 x3ear13 x3ear15 x3eam0 x3eam8 x3eam10 x3eam18 x3eam20 x3eam28 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eamf8 x3eam100 x3eam108 x3eam110 x3eam128 : Nat) (S' : State) : Prop :=
  ∃ x429r10 x429r11 x429r13, L429 s S' x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x429r10 x429r11 x3ear12 x429r13 x3eam0 x3eam8 x3eam10 x3eam18 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eam128 ∧ x429r10 = (x3eam108 + x3ear13) % 18446744073709551616 ∧ x429r11 = (((x3ear11 + x3eam28 + (x3ear15 + x3ear9) / 18446744073709551616) % 18446744073709551616 + x3eam20 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x3eam100 + (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x429r13 = (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_3ea_429 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x3ea)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x3ear9 x3ear11 x3ear12 x3ear13 x3ear15 x3eam0 x3eam8 x3eam10 x3eam18 x3eam20 x3eam28 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eamf8 x3eam100 x3eam108 x3eam110 x3eam128 : Nat) (hL : L3ea s S x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x3ear9 x3ear11 x3ear12 x3ear13 x3ear15 x3eam0 x3eam8 x3eam10 x3eam18 x3eam20 x3eam28 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eamf8 x3eam100 x3eam108 x3eam110 x3eam128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x429)) S (P_3ea_429 s  x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x3ear9 x3ear11 x3ear12 x3ear13 x3ear15 x3eam0 x3eam8 x3eam10 x3eam18 x3eam20 x3eam28 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eamf8 x3eam100 x3eam108 x3eam110 x3eam128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x3earax, hB_x3earax, hE_x3earcx, hB_x3earcx, hE_x3eardx, hB_x3eardx, hE_x3earbx, hB_x3earbx, hE_x3earsi, hB_x3earsi, hE_x3eardi, hB_x3eardi, hE_x3ear8, hB_x3ear8, hE_x3ear9, hB_x3ear9, hE_x3ear11, hB_x3ear11, hE_x3ear12, hB_x3ear12, hE_x3ear13, hB_x3ear13, hE_x3ear15, hB_x3ear15, hE_x3eam0, hB_x3eam0, hE_x3eam8, hB_x3eam8, hE_x3eam10, hB_x3eam10, hE_x3eam18, hB_x3eam18, hE_x3eam20, hB_x3eam20, hE_x3eam28, hB_x3eam28, hE_x3eam30, hB_x3eam30, hE_x3eam60, hB_x3eam60, hE_x3eam68, hB_x3eam68, hE_x3eam88, hB_x3eam88, hE_x3eamc8, hB_x3eamc8, hE_x3eamd0, hB_x3eamd0, hE_x3eamd8, hB_x3eamd8, hE_x3eame0, hB_x3eame0, hE_x3eame8, hB_x3eame8, hE_x3eamf0, hB_x3eamf0, hE_x3eamf8, hB_x3eamf8, hE_x3eam100, hB_x3eam100, hE_x3eam108, hB_x3eam108, hE_x3eam110, hB_x3eam110, hE_x3eam128, hB_x3eam128⟩ := hL
  janus64_run [Util.readLE_32, hE_x3earax, hE_x3earcx, hE_x3eardx, hE_x3earbx, hE_x3earsi, hE_x3eardi, hE_x3ear8, hE_x3ear9, hE_x3ear11, hE_x3ear12, hE_x3ear13, hE_x3ear15, hE_x3eam0, hE_x3eam8, hE_x3eam10, hE_x3eam18, hE_x3eam20, hE_x3eam28, hE_x3eam30, hE_x3eam60, hE_x3eam68, hE_x3eam88, hE_x3eamc8, hE_x3eamd0, hE_x3eamd8, hE_x3eame0, hE_x3eame8, hE_x3eamf0, hE_x3eamf8, hE_x3eam100, hE_x3eam108, hE_x3eam110, hE_x3eam128, hsp4, Nat.mod_eq_of_lt hB_x3earax, Nat.mod_eq_of_lt hB_x3earcx, Nat.mod_eq_of_lt hB_x3eardx, Nat.mod_eq_of_lt hB_x3earbx, Nat.mod_eq_of_lt hB_x3earsi, Nat.mod_eq_of_lt hB_x3eardi, Nat.mod_eq_of_lt hB_x3ear8, Nat.mod_eq_of_lt hB_x3ear9, Nat.mod_eq_of_lt hB_x3ear11, Nat.mod_eq_of_lt hB_x3ear12, Nat.mod_eq_of_lt hB_x3ear13, Nat.mod_eq_of_lt hB_x3ear15, Nat.mod_eq_of_lt hB_x3eam0, Nat.mod_eq_of_lt hB_x3eam8, Nat.mod_eq_of_lt hB_x3eam10, Nat.mod_eq_of_lt hB_x3eam18, Nat.mod_eq_of_lt hB_x3eam20, Nat.mod_eq_of_lt hB_x3eam28, Nat.mod_eq_of_lt hB_x3eam30, Nat.mod_eq_of_lt hB_x3eam60, Nat.mod_eq_of_lt hB_x3eam68, Nat.mod_eq_of_lt hB_x3eam88, Nat.mod_eq_of_lt hB_x3eamc8, Nat.mod_eq_of_lt hB_x3eamd0, Nat.mod_eq_of_lt hB_x3eamd8, Nat.mod_eq_of_lt hB_x3eame0, Nat.mod_eq_of_lt hB_x3eame8, Nat.mod_eq_of_lt hB_x3eamf0, Nat.mod_eq_of_lt hB_x3eamf8, Nat.mod_eq_of_lt hB_x3eam100, Nat.mod_eq_of_lt hB_x3eam108, Nat.mod_eq_of_lt hB_x3eam110, Nat.mod_eq_of_lt hB_x3eam128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_3ea_429
  refine ⟨(x3eam108 + x3ear13) % 18446744073709551616, (((x3ear11 + x3eam28 + (x3ear15 + x3ear9) / 18446744073709551616) % 18446744073709551616 + x3eam20 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x3eam100 + (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L429
    and_intros
    · first | exact hE_x3earax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3earax)
    · exact hB_x3earax
    · first | exact hE_x3earcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3earcx)
    · exact hB_x3earcx
    · first | exact hE_x3eardx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3eardx)
    · exact hB_x3eardx
    · first | exact hE_x3earbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3earbx)
    · exact hB_x3earbx
    · first | exact hE_x3earsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3earsi)
    · exact hB_x3earsi
    · first | exact hE_x3eardi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3eardi)
    · exact hB_x3eardi
    · first | exact hE_x3ear8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3ear8)
    · exact hB_x3ear8
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x3ear12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x3ear12)
    · exact hB_x3ear12
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam0
    · exact hB_x3eam0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam8
    · exact hB_x3eam8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam10
    · exact hB_x3eam10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam18
    · exact hB_x3eam18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam30
    · exact hB_x3eam30
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam60
    · exact hB_x3eam60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam68
    · exact hB_x3eam68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam88
    · exact hB_x3eam88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eamc8
    · exact hB_x3eamc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eamd0
    · exact hB_x3eamd0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eamd8
    · exact hB_x3eamd8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eame0
    · exact hB_x3eame0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eame8
    · exact hB_x3eame8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eamf0
    · exact hB_x3eamf0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x3eam128
    · exact hB_x3eam128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
