import Fv256.Arm64.DecProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

abbrev mm : Nat := segAddr Fv256.Arm64.DecProg.program "runtime.memmove"

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `runtime.memmove(dst, src, n)` for `n ≤ 32` (register-only paths), non-overlapping buffers. -/
theorem memmove_small (s : State) (dst src n ret : Nat) (hn : n ≤ 32) (hd : dst + n ≤ 2 ^ 48) (hs : src + n ≤ 2 ^ 48)
    (hda : s.mem.accessible dst n true = true) (hsa : s.mem.accessible src n false = true)
    (hdisj : dst + n ≤ src ∨ src + n ≤ dst) (hpc : s.pc = BitVec.ofNat 64 mm)
    (e0 : s.regs 0 = BitVec.ofNat 64 dst) (e1 : s.regs 1 = BitVec.ofNat 64 src) (e2 : s.regs 2 = BitVec.ofNat 64 n)
    (hl : s.regs 30 = BitVec.ofNat 64 ret) (hret : ret < 2 ^ 48) (hret4 : ret % 4 = 0) :
    ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 ret) s (fun S' =>
      S'.sp = s.sp ∧ (∀ k, k ∉ [4, 5, 6, 7, 12, 13] → S'.regs k = s.regs k) ∧
      (∀ i, i < n → S'.mem.readLE (dst + i) 1 = s.mem.readLE (src + i) 1) ∧
      MemFrame s.mem S'.mem [(dst, dst + n)]) := by
  have hc : mm + 0x800 < 2 ^ 47 := by decide
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ (8 ≤ n ∧ n ≤ 16) ∨ (17 ≤ n ∧ n ≤ 32)) with h | h | h | h | h | h | h | h | h | h
  · subst h
    janus_run [e0, e1, e2, hl]
    refine ⟨fun k hk => trivial, fun i hi => by omega, MemFrame.refl _ _⟩
  · subst h
    janus_run [e0, e1, e2, hl]
    rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · exact one_copy s.mem dst src 1
    · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 2 2 2 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 2 + dst - 2 = dst + (2 - 2) := by omega
           have e2 : 2 + src - 2 = src + (2 - 2) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 2)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 3 2 2 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 3 + dst - 2 = dst + (3 - 2) := by omega
           have e2 : 3 + src - 2 = src + (3 - 2) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 3)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 4 4 4 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 4 + dst - 4 = dst + (4 - 4) := by omega
           have e2 : 4 + src - 4 = src + (4 - 4) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 4)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 5 4 4 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 5 + dst - 4 = dst + (5 - 4) := by omega
           have e2 : 5 + src - 4 = src + (5 - 4) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 5)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 6 4 4 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 6 + dst - 4 = dst + (6 - 4) := by omega
           have e2 : 6 + src - 4 = src + (6 - 4) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 6)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · subst h
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src 7 4 4 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : 7 + dst - 4 = dst + (7 - 4) := by omega
           have e2 : 7 + src - 4 = src + (7 - 4) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + 7)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · skip
    janus_run [e0, e1, e2, hl]
    try rw [rd_mod64 _ _ _ (by omega)]
    try rw [rd_mod64 _ _ _ (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · have := two_copy' s.mem dst src n 8 8 (by omega) (by omega) (by omega) hdisj
      first
        | simpa using this
        | (have e1 : n + dst - 8 = dst + (n - 8) := by omega
           have e2 : n + src - 8 = src + (n - 8) := by omega
           simp only [e1, e2]
           simpa using this)
    · exact ((MemFrame.refl s.mem [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)
  · janus_run [e0, e1, e2, hl]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [hk]
    · exact copy_blk s.mem dst src n (by omega) (by omega) hdisj
    · exact ((((MemFrame.refl s.mem [(dst, dst + n)]).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
        (List.mem_singleton_self _) (by omega) (by omega)

/-- `memmove_small` as a callee summary. -/
theorem memmove_sum :
    Summary Fv256.Arm64.DecProg.program mm
      (fun s => (s.regs 2).toNat ≤ 32 ∧ (s.regs 0).toNat + (s.regs 2).toNat ≤ 2 ^ 48 ∧
        (s.regs 1).toNat + (s.regs 2).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 0).toNat (s.regs 2).toNat true = true ∧
        s.mem.accessible (s.regs 1).toNat (s.regs 2).toNat false = true ∧
        ((s.regs 0).toNat + (s.regs 2).toNat ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + (s.regs 2).toNat ≤ (s.regs 0).toNat) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => s'.sp = s.sp ∧ (∀ k, k ∉ [4, 5, 6, 7, 12, 13] → s'.regs k = s.regs k) ∧
        (∀ i, i < (s.regs 2).toNat → s'.mem.readLE ((s.regs 0).toNat + i) 1 = s.mem.readLE ((s.regs 1).toNat + i) 1) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)]) := by
  intro s hpc ⟨hn, hd, hs, hda, hsa, hdisj, hret, hret4⟩
  have e0 : s.regs 0 = BitVec.ofNat 64 (s.regs 0).toNat := by simp
  have e1 : s.regs 1 = BitVec.ofNat 64 (s.regs 1).toNat := by simp
  have e2 : s.regs 2 = BitVec.ofNat 64 (s.regs 2).toNat := by simp
  have hl : s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat := by simp
  have hm := memmove_small s (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat (s.regs 30).toNat hn hd hs hda hsa hdisj hpc e0 e1 e2
    hl hret hret4
  rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
  refine reachesRet64_mono hm ?_
  exact fun S h => h
end Fv256.Arm64.Dec
