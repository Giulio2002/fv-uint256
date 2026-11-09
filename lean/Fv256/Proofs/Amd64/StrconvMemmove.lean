import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.DecA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev mm : Nat := segAddr Fv256.DecProg.program "runtime.memmove"

set_option maxHeartbeats 16000000 in
/-- `runtime.memmove(dst, src, n)` for `n ≤ 32` (the register-only paths), non-overlapping buffers. -/
theorem memmove_small (s0 : State) (dst src n sp : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 32) (hd : dst + n ≤ 2 ^ 48) (hs : src + n ≤ 2 ^ 48)
    (hda : M.accessible dst n true = true) (hsa : M.accessible src n false = true)
    (hdisj : dst + n ≤ src ∨ src + n ≤ dst)
    (e0 : R 0 = BitVec.ofNat 64 dst) (e3 : R 3 = BitVec.ofNat 64 src) (e1 : R 1 = BitVec.ofNat 64 n)
    (e4 : R 4 = BitVec.ofNat 64 sp) (hsp : sp + 8 ≤ 2 ^ 48) (hspa : M.accessible sp 8 false = true)
    (hdsp : dst + n ≤ sp ∨ sp + 8 ≤ dst) (hret : M.readLE sp 8 < 2 ^ 47) :
    ReachesRet Fv256.DecProg.program (BitVec.ofNat 64 (M.readLE sp 8))
      { s0 with regs := R, rip := BitVec.ofNat 64 mm, flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (M.readLE sp 8), flags := fl', xmm := X', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 (sp + 8) ∧ (∀ k, k ∉ [0, 1, 3, 4, 6, 7] → R' k = R k) ∧
        (∀ i, 4 ≤ i → X' i = s0.xmm i) ∧ (∀ i, i < n → M'.readLE (dst + i) 1 = M.readLE (src + i) 1) ∧
        MemFrame M M' [(dst, dst + n)] ∧ (TabsOK M → TabsOK M')) := by
  have hc : mm + 0x800 < 2 ^ 47 := by decide
  rcases (by omega : n = 0 ∨ (1 ≤ n ∧ n ≤ 2) ∨ n = 3 ∨ n = 4 ∨ (5 ≤ n ∧ n ≤ 7) ∨ n = 8 ∨ (9 ≤ n ∧ n ≤ 16) ∨ (17 ≤ n ∧ n ≤ 32)) with h | h | h | h | h | h | h | h
  · subst h
    janus64_run [e0, e3, e1, e4]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · intro i hi; omega
    · exact MemFrame.refl _ _
    · exact id
  · janus64_run [e0, e3, e1, e4]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · exact two_copy' M dst src n 1 1 (by omega) (by omega) (by omega) hdisj
    · exact ((MemFrame.refl M [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.two hdl hda (by omega) (by omega) (by omega) (by omega) _ _
  · subst h
    janus64_run [e0, e3, e1, e4]
    have z16 := merge_store16 (BitVec.ofNat 64 dst) (M.readLE src 2) (by simpa using Janus.Arm64.Memory.readLE_lt M src 2)
    have z8 := zx_store 8 (M.readLE (src + 2) 1) (by simpa using Janus.Arm64.Memory.readLE_lt M (src + 2) 1) (by omega)
    simp only [Nat.reducePow] at z8
    rw [z16, z8]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · have := two_copy M dst src 3 2 1 (by omega) (by omega) (by omega) hdisj
      rw [show dst + 3 - 1 = dst + 2 by omega, show src + 3 - 1 = src + 2 by omega] at this
      exact this
    · exact ((MemFrame.refl M [(dst, dst + 3)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.two hdl hda (by omega) (by omega) (by omega) (by omega) _ _
  · subst h
    janus64_run [e0, e3, e1, e4]
    rw [mod32_read]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · exact one_copy M dst src 4
    · exact (MemFrame.refl M [(dst, dst + 4)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.writeLE hdl hda _
  · janus64_run [e0, e3, e1, e4]
    rw [mod32_read, mod32_read]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · exact two_copy' M dst src n 4 4 (by omega) (by omega) (by omega) hdisj
    · exact ((MemFrame.refl M [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.two hdl hda (by omega) (by omega) (by omega) (by omega) _ _
  · subst h
    janus64_run [e0, e3, e1, e4]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · exact one_copy M dst src 8
    · exact (MemFrame.refl M [(dst, dst + 8)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.writeLE hdl hda _
  · janus64_run [e0, e3, e1, e4]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi; rfl
    · exact two_copy' M dst src n 8 8 (by omega) (by omega) (by omega) hdisj
    · exact ((MemFrame.refl M [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.two hdl hda (by omega) (by omega) (by omega) (by omega) _ _
  · janus64_run [e0, e3, e1, e4]
    refine ⟨_, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setRegF]; exact (BitVec.ofNat_add sp 8).symm
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [setRegF, hk]
    · intro i hi
      have h0 : i ≠ 0 := by omega
      have h1 : i ≠ 1 := by omega
      simp [setXmmF, h0, h1]
    · exact two_copy' M dst src n 16 16 (by omega) (by omega) (by omega) hdisj
    · exact ((MemFrame.refl M [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
    · exact fun hdl => TabsOK.two hdl hda (by omega) (by omega) (by omega) (by omega) _ _

/-- `memmove_small` as a callee summary. -/
theorem memmove_sum :
    Summary Fv256.DecProg.program mm
      (fun s => (s.regs 1).toNat ≤ 32 ∧ (s.regs 0).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧
        (s.regs 3).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true ∧
        s.mem.accessible (s.regs 3).toNat (s.regs 1).toNat false = true ∧
        ((s.regs 0).toNat + (s.regs 1).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + (s.regs 1).toNat ≤ (s.regs 0).toNat) ∧
        (s.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        ((s.regs 0).toNat + (s.regs 1).toNat ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 0).toNat) ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ (∀ k, k ∉ [0, 1, 3, 4, 6, 7] → s'.regs k = s.regs k) ∧
        (∀ i, 4 ≤ i → s'.xmm i = s.xmm i) ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        (∀ i, i < (s.regs 1).toNat → s'.mem.readLE ((s.regs 0).toNat + i) 1 = s.mem.readLE ((s.regs 3).toNat + i) 1) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] ∧
        (TabsOK s.mem → TabsOK s'.mem)) := by
  intro s hpc ⟨hn, hd, hs, hda, hsa, hdisj, hsp, hspa, hdsp, hret⟩
  have e0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have e3 : s.regs 3 = BitVec.ofNat 64 (s.regs 3).toNat := by simp
  have e1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by simp
  have e4 : s.regs 4 = BitVec.ofNat 64 (s.regs 4).toNat := by simp
  have hm := memmove_small s (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (s.regs 4).toNat s.regs s.flags s.mem hn hd hs
    hda hsa hdisj e0 e3 e1 e4 hsp hspa hdsp hret
  have hs' : ({ s with regs := s.regs, rip := BitVec.ofNat 64 mm, flags := s.flags, mem := s.mem } : State) = s := by
    cases s; simp at hpc ⊢; exact hpc.symm
  rw [hs'] at hm
  refine ReachesRet.mono hm ?_
  rintro S ⟨R', fl', X', M', rfl, a4, ak, ax, ab, afr, ad⟩
  refine ⟨rfl, ?_, ak, ax, rfl, rfl, ab, afr, ad⟩
  show R' 4 = s.regs 4 + 8
  rw [a4]
  have := (s.regs 4).isLt
  rw [e4, BitVec.ofNat_add]
  simp [BitVec.ofNat_toNat]

end Fv256.Amd64.Dec
