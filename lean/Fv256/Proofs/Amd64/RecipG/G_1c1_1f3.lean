import Fv256.Proofs.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_1c1_1f3 (s : State) (y3 : Nat) (x1c1rax x1c1rcx x1c1rdx x1c1rbx x1c1rsi x1c1rdi x1c1r8 x1c1r9 x1c1r10 x1c1m208 x1c1m210 x1c1m218 x1c1m220 : Nat) (S' : State) : Prop :=
  ∃ x1f3rax x1f3r10 x1f3mb0, L1f3 s S' x1f3rax x1c1rcx x1c1rsi x1c1rdi x1c1r8 x1c1r9 x1f3r10 x1f3mb0 x1c1m208 x1c1m210 x1c1m218 x1c1m220 ∧ x1f3rax = (if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else 0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax)).toNat ∧ x1f3r10 = (if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616)).toNat ∧ x1f3mb0 = (if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else 0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax)) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_1c1_1f3 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x1c1)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x1c1rax x1c1rcx x1c1rdx x1c1rbx x1c1rsi x1c1rdi x1c1r8 x1c1r9 x1c1r10 x1c1m208 x1c1m210 x1c1m218 x1c1m220 : Nat) (hL : L1c1 s S x1c1rax x1c1rcx x1c1rdx x1c1rbx x1c1rsi x1c1rdi x1c1r8 x1c1r9 x1c1r10 x1c1m208 x1c1m210 x1c1m218 x1c1m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x1f3)) S (P_1c1_1f3 s y3 x1c1rax x1c1rcx x1c1rdx x1c1rbx x1c1rsi x1c1rdi x1c1r8 x1c1r9 x1c1r10 x1c1m208 x1c1m210 x1c1m218 x1c1m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x1c1rax, hB_x1c1rax, hE_x1c1rcx, hB_x1c1rcx, hE_x1c1rdx, hB_x1c1rdx, hE_x1c1rbx, hB_x1c1rbx, hE_x1c1rsi, hB_x1c1rsi, hE_x1c1rdi, hB_x1c1rdi, hE_x1c1r8, hB_x1c1r8, hE_x1c1r9, hB_x1c1r9, hE_x1c1r10, hB_x1c1r10, hE_x1c1m208, hB_x1c1m208, hE_x1c1m210, hB_x1c1m210, hE_x1c1m218, hB_x1c1m218, hE_x1c1m220, hB_x1c1m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x1c1rax, hE_x1c1rcx, hE_x1c1rdx, hE_x1c1rbx, hE_x1c1rsi, hE_x1c1rdi, hE_x1c1r8, hE_x1c1r9, hE_x1c1r10, hE_x1c1m208, hE_x1c1m210, hE_x1c1m218, hE_x1c1m220, hsp4, Nat.mod_eq_of_lt hB_x1c1rax, Nat.mod_eq_of_lt hB_x1c1rcx, Nat.mod_eq_of_lt hB_x1c1rdx, Nat.mod_eq_of_lt hB_x1c1rbx, Nat.mod_eq_of_lt hB_x1c1rsi, Nat.mod_eq_of_lt hB_x1c1rdi, Nat.mod_eq_of_lt hB_x1c1r8, Nat.mod_eq_of_lt hB_x1c1r9, Nat.mod_eq_of_lt hB_x1c1r10, Nat.mod_eq_of_lt hB_x1c1m208, Nat.mod_eq_of_lt hB_x1c1m210, Nat.mod_eq_of_lt hB_x1c1m218, Nat.mod_eq_of_lt hB_x1c1m220]
  all_goals (
  unfold P_1c1_1f3
  refine ⟨(if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else 0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax)).toNat, (if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616)).toNat, (if (BitVec.ofNat 64 x1c1rbx ||| (0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax) ||| BitVec.ofNat 64 ((subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + (subFlags (BitVec.ofNat 64 x1c1r10) (BitVec.ofNat 64 x1c1rdx) (decide (0 < x1c1rax))).fst.toNat + ((18446744073709551616 - x1c1rax) % 18446744073709551616 + (18446744073709551616 - x1c1rax) % 18446744073709551616) / 18446744073709551616))).toNat = 0 then 18446744073709551615#64 else 0#64 - BitVec.ofNat 64 x1c1rax + (0#64 - BitVec.ofNat 64 x1c1rax)) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1f3
    and_intros
    · first | rfl | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x1c1rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1c1rcx)
    · exact hB_x1c1rcx
    · first | exact hE_x1c1rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1c1rsi)
    · exact hB_x1c1rsi
    · first | exact hE_x1c1rdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1c1rdi)
    · exact hB_x1c1rdi
    · first | exact hE_x1c1r8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1c1r8)
    · exact hB_x1c1r8
    · first | exact hE_x1c1r9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x1c1r9)
    · exact hB_x1c1r9
    · first | rfl | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow])
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1c1m208
    · exact hB_x1c1m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1c1m210
    · exact hB_x1c1m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1c1m218
    · exact hB_x1c1m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x1c1m220
    · exact hB_x1c1m220
  · rfl
  · rfl
  · rfl
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
