import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_2f8_33e (s : State) (x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128 : Nat) (S' : State) : Prop :=
  ∃ x33erax x33erbx x33ersi x33er9 x33er11 x33er12 x33er13 x33er15 x33em20 x33em28, L33e s S' x33erax x2f8rcx x33erbx x33ersi x2f8rdi x2f8r8 x33er9 x2f8r10 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x2f8m60 x2f8m68 x2f8m88 x2f8m128 ∧ x33erax = (x2f8m70 * x2f8rdx) % 18446744073709551616 ∧ x33erbx = x2f8rax % 18446744073709551616 ∧ x33ersi = x2f8rdx % 18446744073709551616 ∧ x33er9 = (x2f8rdi * x2f8rax) % 18446744073709551616 ∧ x33er11 = (x2f8rdi * x2f8rax / 18446744073709551616 + x2f8rdi * x2f8rdx) % 18446744073709551616 ∧ x33er12 = x2f8m70 % 18446744073709551616 ∧ x33er13 = (x2f8m70 * x2f8rax) % 18446744073709551616 ∧ x33er15 = (x2f8m70 * x2f8rax / 18446744073709551616) % 18446744073709551616 ∧ x33em20 = (x2f8m70 * x2f8rdx / 18446744073709551616) % 18446744073709551616 ∧ x33em28 = (x2f8m70 * x2f8rcx) % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_2f8_33e (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x2f8)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128 : Nat) (hL : L2f8 s S x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x33e)) S (P_2f8_33e s  x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x2f8rax, hB_x2f8rax, hE_x2f8rcx, hB_x2f8rcx, hE_x2f8rdx, hB_x2f8rdx, hE_x2f8rdi, hB_x2f8rdi, hE_x2f8r8, hB_x2f8r8, hE_x2f8r10, hB_x2f8r10, hE_x2f8m0, hB_x2f8m0, hE_x2f8m8, hB_x2f8m8, hE_x2f8m10, hB_x2f8m10, hE_x2f8m18, hB_x2f8m18, hE_x2f8m60, hB_x2f8m60, hE_x2f8m68, hB_x2f8m68, hE_x2f8m70, hB_x2f8m70, hE_x2f8m88, hB_x2f8m88, hE_x2f8m128, hB_x2f8m128⟩ := hL
  janus64_run [Util.readLE_32, hE_x2f8rax, hE_x2f8rcx, hE_x2f8rdx, hE_x2f8rdi, hE_x2f8r8, hE_x2f8r10, hE_x2f8m0, hE_x2f8m8, hE_x2f8m10, hE_x2f8m18, hE_x2f8m60, hE_x2f8m68, hE_x2f8m70, hE_x2f8m88, hE_x2f8m128, hsp4, Nat.mod_eq_of_lt hB_x2f8rax, Nat.mod_eq_of_lt hB_x2f8rcx, Nat.mod_eq_of_lt hB_x2f8rdx, Nat.mod_eq_of_lt hB_x2f8rdi, Nat.mod_eq_of_lt hB_x2f8r8, Nat.mod_eq_of_lt hB_x2f8r10, Nat.mod_eq_of_lt hB_x2f8m0, Nat.mod_eq_of_lt hB_x2f8m8, Nat.mod_eq_of_lt hB_x2f8m10, Nat.mod_eq_of_lt hB_x2f8m18, Nat.mod_eq_of_lt hB_x2f8m60, Nat.mod_eq_of_lt hB_x2f8m68, Nat.mod_eq_of_lt hB_x2f8m70, Nat.mod_eq_of_lt hB_x2f8m88, Nat.mod_eq_of_lt hB_x2f8m128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_2f8_33e
  refine ⟨(x2f8m70 * x2f8rdx) % 18446744073709551616, x2f8rax % 18446744073709551616, x2f8rdx % 18446744073709551616, (x2f8rdi * x2f8rax) % 18446744073709551616, (x2f8rdi * x2f8rax / 18446744073709551616 + x2f8rdi * x2f8rdx) % 18446744073709551616, x2f8m70 % 18446744073709551616, (x2f8m70 * x2f8rax) % 18446744073709551616, (x2f8m70 * x2f8rax / 18446744073709551616) % 18446744073709551616, (x2f8m70 * x2f8rdx / 18446744073709551616) % 18446744073709551616, (x2f8m70 * x2f8rcx) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L33e
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x2f8rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x2f8rcx)
    · exact hB_x2f8rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x2f8rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x2f8rdi)
    · exact hB_x2f8rdi
    · first | exact hE_x2f8r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x2f8r8)
    · exact hB_x2f8r8
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | exact hE_x2f8r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x2f8r10)
    · exact hB_x2f8r10
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m0
    · exact hB_x2f8m0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m8
    · exact hB_x2f8m8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m10
    · exact hB_x2f8m10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m18
    · exact hB_x2f8m18
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m60
    · exact hB_x2f8m60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m68
    · exact hB_x2f8m68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m88
    · exact hB_x2f8m88
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x2f8m128
    · exact hB_x2f8m128
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
