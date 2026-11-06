import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_160_1c1 (s : State) (y3 : Nat) (x160rax x160rcx x160rbx x160rsi x160rdi x160r8 x160r9 x160m208 x160m210 x160m218 x160m220 : Nat) (S' : State) : Prop :=
  ∃ x1c1rax x1c1rdx x1c1r10, L1c1 s S' x1c1rax x160rcx x1c1rdx x160rbx x160rsi x160rdi x160r8 x160r9 x1c1r10 x160m208 x160m210 x160m218 x160m220 ∧ x1c1rax = ((x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1c1rdx = (x160rsi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + (x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 + ((x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 ∧ x1c1r10 = x160rax % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_160_1c1 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x160)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x160rax x160rcx x160rbx x160rsi x160rdi x160r8 x160r9 x160m208 x160m210 x160m218 x160m220 : Nat) (hL : L160 s S x160rax x160rcx x160rbx x160rsi x160rdi x160r8 x160r9 x160m208 x160m210 x160m218 x160m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1c1)) S (P_160_1c1 s y3 x160rax x160rcx x160rbx x160rsi x160rdi x160r8 x160r9 x160m208 x160m210 x160m218 x160m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x160rax, hB_x160rax, hE_x160rcx, hB_x160rcx, hE_x160rbx, hB_x160rbx, hE_x160rsi, hB_x160rsi, hE_x160rdi, hB_x160rdi, hE_x160r8, hB_x160r8, hE_x160r9, hB_x160r9, hE_x160m208, hB_x160m208, hE_x160m210, hB_x160m210, hE_x160m218, hB_x160m218, hE_x160m220, hB_x160m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x160rax, hE_x160rcx, hE_x160rbx, hE_x160rsi, hE_x160rdi, hE_x160r8, hE_x160r9, hE_x160m208, hE_x160m210, hE_x160m218, hE_x160m220, hsp4, Nat.mod_eq_of_lt hB_x160rax, Nat.mod_eq_of_lt hB_x160rcx, Nat.mod_eq_of_lt hB_x160rbx, Nat.mod_eq_of_lt hB_x160rsi, Nat.mod_eq_of_lt hB_x160rdi, Nat.mod_eq_of_lt hB_x160r8, Nat.mod_eq_of_lt hB_x160r9, Nat.mod_eq_of_lt hB_x160m208, Nat.mod_eq_of_lt hB_x160m210, Nat.mod_eq_of_lt hB_x160m218, Nat.mod_eq_of_lt hB_x160m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (
  unfold P_160_1c1
  refine ⟨((x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616, (x160rsi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + (x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616 + ((x160rsi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616 + x160rax * x160rax % 18446744073709551616 * x160rsi / 18446744073709551616 + (x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) / 18446744073709551616 + ((x160rax * x160rax % 18446744073709551616 * x160rsi % 18446744073709551616 + x160rdi * (x160rax * x160rax % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x160rdi * (x160rax * x160rax / 18446744073709551616) % 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616, x160rax % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1c1
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x160rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160rcx)
    · exact hB_x160rcx
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x160rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160rbx)
    · exact hB_x160rbx
    · first | exact hE_x160rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160rsi)
    · exact hB_x160rsi
    · first | exact hE_x160rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160rdi)
    · exact hB_x160rdi
    · first | exact hE_x160r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160r8)
    · exact hB_x160r8
    · first | exact hE_x160r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x160r9)
    · exact hB_x160r9
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x160m208
    · exact hB_x160m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x160m210
    · exact hB_x160m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x160m218
    · exact hB_x160m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x160m220
    · exact hB_x160m220
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold RecRegs
    and_intros
    · simp [setRegF, hr4]
    · simp [setRegF, hr5]
    · simp [setRegF, hr14]
    · simp [hx]
  · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.RecipSeg
