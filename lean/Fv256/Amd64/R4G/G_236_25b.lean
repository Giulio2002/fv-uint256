import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_236_25b (s : State) (x236rax x236rcx x236rdx x236rsi x236rdi x236r8 x236r9 x236r10 x236r11 x236r12 x236r13 x236r15 x236m0 x236m8 x236m10 x236m18 x236m40 x236m60 x236m68 x236m70 x236m78 x236m80 x236m88 x236m90 x236m98 x236ma0 x236ma8 x236mb0 x236mb8 x236mc0 x236mc8 x236md0 x236md8 x236me0 x236me8 x236m128 : Nat) (S' : State) : Prop :=
  ∃ x25brbx x25br12 x25br13 x25br15, L25b s S' x236rax x236rdx x25brbx x236rsi x236rdi x236r8 x236r9 x236r10 x236r11 x25br12 x25br13 x25br15 x236m0 x236m8 x236m10 x236m18 x236m40 x236m60 x236m68 x236m70 x236m78 x236m88 x236m90 x236m98 x236ma0 x236ma8 x236mb0 x236mb8 x236mc0 x236mc8 x236md0 x236md8 x236m128 ∧ x25brbx = (x236m80 + x236r15) % 18446744073709551616 ∧ x25br12 = (x236me8 + x236rcx + (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x25br13 = (x236r13 + (x236me8 + x236rcx + (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x25br15 = (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_236_25b (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x236)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x236rax x236rcx x236rdx x236rsi x236rdi x236r8 x236r9 x236r10 x236r11 x236r12 x236r13 x236r15 x236m0 x236m8 x236m10 x236m18 x236m40 x236m60 x236m68 x236m70 x236m78 x236m80 x236m88 x236m90 x236m98 x236ma0 x236ma8 x236mb0 x236mb8 x236mc0 x236mc8 x236md0 x236md8 x236me0 x236me8 x236m128 : Nat) (hL : L236 s S x236rax x236rcx x236rdx x236rsi x236rdi x236r8 x236r9 x236r10 x236r11 x236r12 x236r13 x236r15 x236m0 x236m8 x236m10 x236m18 x236m40 x236m60 x236m68 x236m70 x236m78 x236m80 x236m88 x236m90 x236m98 x236ma0 x236ma8 x236mb0 x236mb8 x236mc0 x236mc8 x236md0 x236md8 x236me0 x236me8 x236m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x25b)) S (P_236_25b s  x236rax x236rcx x236rdx x236rsi x236rdi x236r8 x236r9 x236r10 x236r11 x236r12 x236r13 x236r15 x236m0 x236m8 x236m10 x236m18 x236m40 x236m60 x236m68 x236m70 x236m78 x236m80 x236m88 x236m90 x236m98 x236ma0 x236ma8 x236mb0 x236mb8 x236mc0 x236mc8 x236md0 x236md8 x236me0 x236me8 x236m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x236rax, hB_x236rax, hE_x236rcx, hB_x236rcx, hE_x236rdx, hB_x236rdx, hE_x236rsi, hB_x236rsi, hE_x236rdi, hB_x236rdi, hE_x236r8, hB_x236r8, hE_x236r9, hB_x236r9, hE_x236r10, hB_x236r10, hE_x236r11, hB_x236r11, hE_x236r12, hB_x236r12, hE_x236r13, hB_x236r13, hE_x236r15, hB_x236r15, hE_x236m0, hB_x236m0, hE_x236m8, hB_x236m8, hE_x236m10, hB_x236m10, hE_x236m18, hB_x236m18, hE_x236m40, hB_x236m40, hE_x236m60, hB_x236m60, hE_x236m68, hB_x236m68, hE_x236m70, hB_x236m70, hE_x236m78, hB_x236m78, hE_x236m80, hB_x236m80, hE_x236m88, hB_x236m88, hE_x236m90, hB_x236m90, hE_x236m98, hB_x236m98, hE_x236ma0, hB_x236ma0, hE_x236ma8, hB_x236ma8, hE_x236mb0, hB_x236mb0, hE_x236mb8, hB_x236mb8, hE_x236mc0, hB_x236mc0, hE_x236mc8, hB_x236mc8, hE_x236md0, hB_x236md0, hE_x236md8, hB_x236md8, hE_x236me0, hB_x236me0, hE_x236me8, hB_x236me8, hE_x236m128, hB_x236m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x236rax, hE_x236rcx, hE_x236rdx, hE_x236rsi, hE_x236rdi, hE_x236r8, hE_x236r9, hE_x236r10, hE_x236r11, hE_x236r12, hE_x236r13, hE_x236r15, hE_x236m0, hE_x236m8, hE_x236m10, hE_x236m18, hE_x236m40, hE_x236m60, hE_x236m68, hE_x236m70, hE_x236m78, hE_x236m80, hE_x236m88, hE_x236m90, hE_x236m98, hE_x236ma0, hE_x236ma8, hE_x236mb0, hE_x236mb8, hE_x236mc0, hE_x236mc8, hE_x236md0, hE_x236md8, hE_x236me0, hE_x236me8, hE_x236m128, hsp4, Nat.mod_eq_of_lt hB_x236rax, Nat.mod_eq_of_lt hB_x236rcx, Nat.mod_eq_of_lt hB_x236rdx, Nat.mod_eq_of_lt hB_x236rsi, Nat.mod_eq_of_lt hB_x236rdi, Nat.mod_eq_of_lt hB_x236r8, Nat.mod_eq_of_lt hB_x236r9, Nat.mod_eq_of_lt hB_x236r10, Nat.mod_eq_of_lt hB_x236r11, Nat.mod_eq_of_lt hB_x236r12, Nat.mod_eq_of_lt hB_x236r13, Nat.mod_eq_of_lt hB_x236r15, Nat.mod_eq_of_lt hB_x236m0, Nat.mod_eq_of_lt hB_x236m8, Nat.mod_eq_of_lt hB_x236m10, Nat.mod_eq_of_lt hB_x236m18, Nat.mod_eq_of_lt hB_x236m40, Nat.mod_eq_of_lt hB_x236m60, Nat.mod_eq_of_lt hB_x236m68, Nat.mod_eq_of_lt hB_x236m70, Nat.mod_eq_of_lt hB_x236m78, Nat.mod_eq_of_lt hB_x236m80, Nat.mod_eq_of_lt hB_x236m88, Nat.mod_eq_of_lt hB_x236m90, Nat.mod_eq_of_lt hB_x236m98, Nat.mod_eq_of_lt hB_x236ma0, Nat.mod_eq_of_lt hB_x236ma8, Nat.mod_eq_of_lt hB_x236mb0, Nat.mod_eq_of_lt hB_x236mb8, Nat.mod_eq_of_lt hB_x236mc0, Nat.mod_eq_of_lt hB_x236mc8, Nat.mod_eq_of_lt hB_x236md0, Nat.mod_eq_of_lt hB_x236md8, Nat.mod_eq_of_lt hB_x236me0, Nat.mod_eq_of_lt hB_x236me8, Nat.mod_eq_of_lt hB_x236m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_236_25b
  refine ⟨(x236m80 + x236r15) % 18446744073709551616, (x236me8 + x236rcx + (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x236r13 + (x236me8 + x236rcx + (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x236me0 + x236r12 + (x236m80 + x236r15) / 18446744073709551616) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L25b
    and_intros
    · first | exact hE_x236rax | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236rax)
    · exact hB_x236rax
    · first | exact hE_x236rdx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236rdx)
    · exact hB_x236rdx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x236rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236rsi)
    · exact hB_x236rsi
    · first | exact hE_x236rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236rdi)
    · exact hB_x236rdi
    · first | exact hE_x236r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236r8)
    · exact hB_x236r8
    · first | exact hE_x236r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236r9)
    · exact hB_x236r9
    · first | exact hE_x236r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236r10)
    · exact hB_x236r10
    · first | exact hE_x236r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x236r11)
    · exact hB_x236r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m0
    · exact hB_x236m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m8
    · exact hB_x236m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m10
    · exact hB_x236m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m18
    · exact hB_x236m18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m40
    · exact hB_x236m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m60
    · exact hB_x236m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m68
    · exact hB_x236m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m70
    · exact hB_x236m70
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m78
    · exact hB_x236m78
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m88
    · exact hB_x236m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m90
    · exact hB_x236m90
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m98
    · exact hB_x236m98
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236ma0
    · exact hB_x236ma0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236ma8
    · exact hB_x236ma8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236mb0
    · exact hB_x236mb0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236mb8
    · exact hB_x236mb8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236mc0
    · exact hB_x236mc0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236mc8
    · exact hB_x236mc8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236md0
    · exact hB_x236md0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236md8
    · exact hB_x236md8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x236m128
    · exact hB_x236m128
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
