import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_b47_b9f (s : State) (y3 : Nat) (xb47rax xb47rcx xb47rdx xb47rbx xb47rsi xb47r8 xb47r10 xb47r12 xb47r13 xb47r15 xb47m40 xb47m48 xb47m50 xb47m60 xb47m100 : Nat) (S' : State) : Prop :=
  ∃ xb9frdx, Lb9f s S' xb47rcx xb9frdx xb47rbx xb47m40 xb47m48 xb47m50 xb47m60 ∧ xb9frdx = (if 4611686018427387904 < xb47r13 + (decide (0 < xb47rdx + (decide (0 < xb47rax + (decide (0 < xb47r15 + (decide (0 < xb47r8 + (decide (0 < xb47r10 + (decide (0 < xb47r12 + (decide (0 < xb47rsi + (decide (0 < xb47m100)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat then 1 else 0) ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_b47_b9f {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xb47)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xb47rax xb47rcx xb47rdx xb47rbx xb47rsi xb47r8 xb47r10 xb47r12 xb47r13 xb47r15 xb47m40 xb47m48 xb47m50 xb47m60 xb47m100 : Nat) (hL : Lb47 s S xb47rax xb47rcx xb47rdx xb47rbx xb47rsi xb47r8 xb47r10 xb47r12 xb47r13 xb47r15 xb47m40 xb47m48 xb47m50 xb47m60 xb47m100) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xb9f)) S (P_b47_b9f s y3 xb47rax xb47rcx xb47rdx xb47rbx xb47rsi xb47r8 xb47r10 xb47r12 xb47r13 xb47r15 xb47m40 xb47m48 xb47m50 xb47m60 xb47m100) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xb47rax, hB_xb47rax, hE_xb47rcx, hB_xb47rcx, hE_xb47rdx, hB_xb47rdx, hE_xb47rbx, hB_xb47rbx, hE_xb47rsi, hB_xb47rsi, hE_xb47r8, hB_xb47r8, hE_xb47r10, hB_xb47r10, hE_xb47r12, hB_xb47r12, hE_xb47r13, hB_xb47r13, hE_xb47r15, hB_xb47r15, hE_xb47m40, hB_xb47m40, hE_xb47m48, hB_xb47m48, hE_xb47m50, hB_xb47m50, hE_xb47m60, hB_xb47m60, hE_xb47m100, hB_xb47m100⟩ := hL
  janus64_run [Util.readLE_32, hE_xb47rax, hE_xb47rcx, hE_xb47rdx, hE_xb47rbx, hE_xb47rsi, hE_xb47r8, hE_xb47r10, hE_xb47r12, hE_xb47r13, hE_xb47r15, hE_xb47m40, hE_xb47m48, hE_xb47m50, hE_xb47m60, hE_xb47m100, hsp4, Nat.mod_eq_of_lt hB_xb47rax, Nat.mod_eq_of_lt hB_xb47rcx, Nat.mod_eq_of_lt hB_xb47rdx, Nat.mod_eq_of_lt hB_xb47rbx, Nat.mod_eq_of_lt hB_xb47rsi, Nat.mod_eq_of_lt hB_xb47r8, Nat.mod_eq_of_lt hB_xb47r10, Nat.mod_eq_of_lt hB_xb47r12, Nat.mod_eq_of_lt hB_xb47r13, Nat.mod_eq_of_lt hB_xb47r15, Nat.mod_eq_of_lt hB_xb47m40, Nat.mod_eq_of_lt hB_xb47m48, Nat.mod_eq_of_lt hB_xb47m50, Nat.mod_eq_of_lt hB_xb47m60, Nat.mod_eq_of_lt hB_xb47m100]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_b47_b9f
  refine ⟨(if 4611686018427387904 < xb47r13 + (decide (0 < xb47rdx + (decide (0 < xb47rax + (decide (0 < xb47r15 + (decide (0 < xb47r8 + (decide (0 < xb47r10 + (decide (0 < xb47r12 + (decide (0 < xb47rsi + (decide (0 < xb47m100)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat)).toNat then 1 else 0), ?_, ?_, ?_, ?_⟩
  · unfold Lb9f
    and_intros
    · first | exact hE_xb47rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb47rcx)
    · exact hB_xb47rcx
    · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; split <;> rfl
    · split <;> decide
    · first | exact hE_xb47rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_xb47rbx)
    · exact hB_xb47rbx
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb47m40
    · exact hB_xb47m40
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb47m48
    · exact hB_xb47m48
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb47m50
    · exact hB_xb47m50
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_xb47m60
    · exact hB_xb47m60
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
