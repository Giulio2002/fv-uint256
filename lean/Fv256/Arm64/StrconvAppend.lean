import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecL
import Fv256.Arm64.StrconvMemmove

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

abbrev au : Nat := segAddr Extracted.program "internal/strconv.AppendUint"

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `strconv.AppendUint(dst, i, 10)` when the result fits in `cap(dst)` (no `growslice`): appends the decimal digits of `i` (arm64). -/
theorem append_summary :
    Summary Extracted.program au
      (fun s => s.regs 4 = 10#64 ∧ GuardOK s 128 ∧ s.sp.toNat % 16 = 0 ∧ 152 ≤ s.sp.toNat ∧ s.sp.toNat + 32 < 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 152) (152 + 32) true = true ∧ TabsOK s.mem ∧
        (s.regs 1).toNat + decLen (s.regs 3).toNat ≤ (s.regs 2).toNat ∧
        (s.regs 0).toNat + (s.regs 2).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (s.regs 2).toNat true = true ∧
        ((s.regs 0).toNat + (s.regs 2).toNat ≤ s.sp.toNat - 152 ∨ s.sp.toNat + 32 ≤ (s.regs 0).toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 152 ∨ s.sp.toNat + 32 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ (s'.regs 1).toNat = (s.regs 1).toNat + decLen (s.regs 3).toNat ∧
        s'.regs 2 = s.regs 2 ∧ s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧
        (∀ k, k < decLen (s.regs 3).toNat →
          s'.mem.readLE ((s.regs 0).toNat + (s.regs 1).toNat + decLen (s.regs 3).toNat - 1 - k) 1 =
            48 + (s.regs 3).toNat / 10 ^ k % 10) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat + (s.regs 1).toNat,
            (s.regs 0).toNat + (s.regs 1).toNat + decLen (s.regs 3).toNat),
          ((s.sp.toNat - 152, s.sp.toNat - 8)), (s.sp.toNat + 8, s.sp.toNat + 32)] ∧ TabsOK s'.mem) := by
  intro s hpc ⟨hbase, hg, hal, h152, hsp2, hw, hd, hcap, hdn, hda, hdisj, hgd, hret, hret4⟩
  have hc : au + 0x300 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  tabs_data hd [hw, hda]
  by_cases h100 : (s.regs 3).toNat < 100
  · by_cases h10 : (s.regs 3).toNat < 10
    · have hl : decLen (s.regs 3).toNat = 1 := decLen_lt _ h10
      dsimp only
      rw [hl] at hcap ⊢
      rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
      janus_run [hbase] calls [memmove_sum]
      rename_i hpc' hsp' hk hby hfr hbr2
      have hd0 := hd.dig (s.regs 3).toNat h10
      have hs := s.sp.isLt
      have hacc1 : ∀ a n, s.sp.toNat - 152 ≤ a → a + n ≤ s.sp.toNat + 32 → s.mem.accessible a n true = true :=
        fun a n h1 h2 => accessible_sub hw (Or.inr rfl) h1 (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        have hb := hby 0 (by omega)
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hb
        rw [Nat.sub_zero, show (s.regs 0).toNat + (s.regs 1).toNat = (s.regs 0).toNat + (s.regs 1).toNat + 0 by omega, hb, Nat.add_zero, hd0]
        simp only [Nat.pow_zero, Nat.div_one]; omega
      · refine MemFrame.trans (rs := [((s.regs 0).toNat + (s.regs 1).toNat, (s.regs 0).toNat + (s.regs 1).toNat + 1),
            (s.sp.toNat - 152, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32)]) ?_ hfr ?_
        · repeat' first
            | exact MemFrame.refl _ _
            | (refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by omega) (by omega))
            | (refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (by omega) (by omega))
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          exact ⟨h, h.1⟩
      · refine TabsOK.frame ?_ hfr ?_
        · repeat' first
            | exact hd
            | refine TabsOK.writeLE ?_ ?_ _
            | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc1 _ _ (by omega) (by omega))
            | exact hacc1 _ _ (by omega) (by omega)
        · sorry

    · have hl : decLen (s.regs 3).toNat = 2 := by
        rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
      dsimp only
      rw [hl] at hcap ⊢
      rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
      janus_run [hbase] calls [memmove_sum]
      rename_i hpc' hsp' hk hby hfr hbr2
      have hsr := hd.sm (s.regs 3).toNat h100
      have hs := s.sp.isLt
      have hacc1 : ∀ a n, s.sp.toNat - 152 ≤ a → a + n ≤ s.sp.toNat + 32 → s.mem.accessible a n true = true :=
        fun a n h1 h2 => accessible_sub hw (Or.inr rfl) h1 (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
        · have hb := hby 1 (by omega)
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hb
          rw [show (s.regs 0).toNat + (s.regs 1).toNat + 1 - 0 = (s.regs 0).toNat + (s.regs 1).toNat + 1 by omega, hb, hsr.2]
          simp only [Nat.pow_zero, Nat.div_one]; try omega
        · have hb := hby 0 (by omega)
          simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hb
          rw [show (s.regs 0).toNat + (s.regs 1).toNat + 1 - 1 = (s.regs 0).toNat + (s.regs 1).toNat + 0 by omega, hb, Nat.add_zero, hsr.1]
          simp only [Nat.pow_one]; omega
      · refine MemFrame.trans (rs := [((s.regs 0).toNat + (s.regs 1).toNat, (s.regs 0).toNat + (s.regs 1).toNat + 2),
            (s.sp.toNat - 152, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32)]) ?_ hfr ?_
        · repeat' first
            | exact MemFrame.refl _ _
            | (refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by omega) (by omega))
            | (refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (by omega) (by omega))
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          exact ⟨h, h.1⟩
      · refine TabsOK.frame ?_ hfr ?_
        · repeat' first
            | exact hd
            | refine TabsOK.writeLE ?_ ?_ _
            | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc1 _ _ (by omega) (by omega))
            | exact hacc1 _ _ (by omega) (by omega)
        · sorry

  · have hge : 100 ≤ (s.regs 3).toNat := by omega
    have hu64 := (s.regs 3).isLt
    have hdl20 := decLen_le_20 _ hu64
    have hnd1 := decLen_pos (s.regs 3).toNat
    have hs := s.sp.isLt
    dsimp only
    rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
    janus_run [hbase] until [fb]
    refine ReachesRet.call fb10_summary ?_ ?_ ?_
    · rfl
    · all_goals (try dsimp only)
      have h128 := toNat_sub_lit s.sp 128 (by omega)
      have h72 := toNat_sub_lit s.sp 72 (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try dsimp only)
      all_goals (try simp only [setReg])
      all_goals (try trace_state)
      all_goals sorry
    · sorry
end Fv256.Arm64.Dec
