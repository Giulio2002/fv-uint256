import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecM
import Fv256.Amd64.StrconvMemmove

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev au : Nat := segAddr Extracted.program "internal/strconv.AppendUint"

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- `strconv.AppendUint(dst, i, 10)` when the result fits in `cap(dst)` (no `growslice`): appends the decimal digits of `i`. -/
theorem append_summary :
    Summary Extracted.program au
      (fun s => s.regs 6 = 10#64 ∧ StackGuardOK s 0 ∧ StackWritable s 0x88 0x20 ∧ (s.regs 4).toNat % 8 = 0 ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ TabsOK s.mem ∧
        (s.regs 3).toNat + decLen (s.regs 7).toNat ≤ (s.regs 1).toNat ∧
        (s.regs 0).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true ∧
        ((s.regs 0).toNat + (s.regs 1).toNat ≤ (s.regs 4).toNat - 0x88 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 0).toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 0x88 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ (s'.regs 3).toNat = (s.regs 3).toNat + decLen (s.regs 7).toNat ∧
        s'.regs 1 = s.regs 1 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        (∀ k, k < decLen (s.regs 7).toNat →
          s'.mem.readLE ((s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat - 1 - k) 1 =
            48 + (s.regs 7).toNat / 10 ^ k % 10) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat + (s.regs 3).toNat,
            (s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat),
          ((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)] ∧
        TabsOK s'.mem) := by
  intro s hpc ⟨hbase, hg, hw, hal, hret, hd, hcap, hdn, hda, hdisj, hgrt⟩
  have hc : au + 0x300 < 2 ^ 47 := by decide
  obtain ⟨hwb, hwn, hwa⟩ := hw
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hret hdisj hgrt
  tabs_data hd [hwa, hda]
  have hs4 := (s.regs 4).isLt
  have hu64 := (s.regs 7).isLt
  have hdl20 := decLen_le_20 (s.regs 7).toNat hu64
  have hnd1 := decLen_pos (s.regs 7).toNat
  by_cases h100 : (s.regs 7).toNat < 100
  · -- small: one `memmove` of 1 or 2 bytes from a read-only table
    have hnd2 : decLen (s.regs 7).toNat ≤ 2 := by
      by_cases h10 : (s.regs 7).toNat < 10
      · rw [decLen_lt _ h10]; omega
      · rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]; omega
    have hdigs : ∀ i, i < decLen (s.regs 7).toNat → ∀ M : Memory, TabsOK M →
        M.readLE ((if (s.regs 7).toNat < 10 then 5163273 + (s.regs 7).toNat else 5176582 + 2 * (s.regs 7).toNat) + i) 1 =
          48 + (s.regs 7).toNat / 10 ^ (decLen (s.regs 7).toNat - 1 - i) % 10 := by
      intro i hi M hM
      by_cases h10 : (s.regs 7).toNat < 10
      · have hl : decLen (s.regs 7).toNat = 1 := decLen_lt _ h10
        have hi0 : i = 0 := by omega
        subst hi0
        rw [if_pos h10, Nat.add_zero, hM.digits _ h10, hl]
        simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]; omega
      · have hl : decLen (s.regs 7).toNat = 2 := by
          rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
        have hsr := hM.smalls (s.regs 7).toNat h100
        rw [if_neg h10, hl]
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [Nat.add_zero, hsr.1]
          have : 10 ^ (2 - 1 - 0) = 10 := by decide
          rw [this]; omega
        · rw [hsr.2]
          have : 10 ^ (2 - 1 - 1) = 1 := by decide
          rw [this]; omega
    by_cases h10 : (s.regs 7).toNat < 10
    · have hl : decLen (s.regs 7).toNat = 1 := decLen_lt _ h10
      dsimp only
      rw [hl] at hcap ⊢
      janus64_run [hbase] calls [memmove_sum]
      rename_i a0 hrip hr4 hx hdf hmx hdl hrg hby hfr
      have hrdk : ∀ k, k < 1 → s'.mem.readLE ((s.regs 0).toNat + (s.regs 3).toNat + 1 - 1 - k) 1 =
          48 + (s.regs 7).toNat / 10 ^ k % 10 := by
        intro k hk
        have hb := hby (1 - 1 - k) (by omega)
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hb
        have h2 := hdigs (1 - 1 - k) (by omega) s.mem hd
        rw [hl] at h2
        rw [show (s.regs 0).toNat + (s.regs 3).toNat + 1 - 1 - k = (s.regs 0).toNat + (s.regs 3).toNat + (1 - 1 - k) by omega, hb]
        rw [if_pos h10] at h2
        rw [show 1 - 1 - (1 - 1 - k) = k by omega] at h2
        rw [← h2]
        try (congr 1; omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := hrg 14 (by simp)
        simpa using this
      · exact hx 15 (by omega)
      · exact hrdk
      · refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)]) ?_ hfr ?_
        · exact (((((((MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
      · refine hdl ?_
        refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE
          (TabsOK.writeLE (TabsOK.writeLE hd ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _
        all_goals first
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    · have hl : decLen (s.regs 7).toNat = 2 := by
        rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
      dsimp only
      rw [hl] at hcap ⊢
      janus64_run [hbase] calls [memmove_sum]
      rename_i a0 hrip hr4 hx hdf hmx hdl hrg hby hfr
      have hrdk : ∀ k, k < 2 → s'.mem.readLE ((s.regs 0).toNat + (s.regs 3).toNat + 2 - 1 - k) 1 =
          48 + (s.regs 7).toNat / 10 ^ k % 10 := by
        intro k hk
        have hb := hby (2 - 1 - k) (by omega)
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hb
        have h2 := hdigs (2 - 1 - k) (by omega) s.mem hd
        rw [hl] at h2
        rw [show (s.regs 0).toNat + (s.regs 3).toNat + 2 - 1 - k = (s.regs 0).toNat + (s.regs 3).toNat + (2 - 1 - k) by omega, hb]
        rw [if_neg h10] at h2
        rw [show 2 - 1 - (2 - 1 - k) = k by omega] at h2
        rw [← h2]
        try (congr 1; omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := hrg 14 (by simp)
        simpa using this
      · exact hx 15 (by omega)
      · exact hrdk
      · refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)]) ?_ hfr ?_
        · exact (((((((MemFrame.refl s.mem _).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)).writeLE _
            (List.mem_singleton_self _) (by omega) (by omega)).writeLE _ (List.mem_singleton_self _) (by omega) (by omega)
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
      · refine hdl ?_
        refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE
          (TabsOK.writeLE (TabsOK.writeLE hd ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _
        all_goals first
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
  · have hge : 100 ≤ (s.regs 7).toNat := by omega
    janus64_run [hbase] until [fb]
    refine ReachesRet.call fb10_summary ?_ ?_ ?_
    · rfl
    · have h72 := toNat_sub_lit (s.regs 4) 72 (by omega)
      have h128 := toNat_sub_lit (s.regs 4) 128 (by omega)
      have h8 := toNat_sub_lit (s.regs 4) 8 (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, h72]; omega
      · simp only [Janus.Arm64.Memory.accessible_writeLE]
        simp [setRegF, h72]
        exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      · simp [setRegF]; omega
      · simp [setRegF, h128]; omega
      · simp [setRegF, h128]; omega
      · simp only [Janus.Arm64.Memory.accessible_writeLE]
        simp [setRegF, h128]
        exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      · refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE (TabsOK.writeLE
          (TabsOK.writeLE (TabsOK.writeLE hd ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _
        all_goals first
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      · simp [setRegF, h72, h128]; omega
      · simp [setRegF, h128]
        rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro s' hrip ⟨b0, b4, b5, b14, bx, bdf, bmx, bdig, bfr, bdl⟩
      simp [setRegF] at b0 b4 b5 b14 bx bdig bfr
      have e72 : (18446744073709551544 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 72 := by omega
      have e128 : (18446744073709551488 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 128 := by omega
      simp only [e72, e128] at bfr bdig
      have bdig2 : ∀ k, k < decLen (s.regs 7).toNat → s'.mem.readLE ((s.regs 4).toNat - 72 + 23 - k) 1 = 48 + (s.regs 7).toNat / 10 ^ k % 10 := by
        intro k hk
        rw [Janus.Arm64.Memory.readLE_one]; exact bdig k hk
      have hb0' : (s'.regs 0).toNat = 24 - decLen (s.regs 7).toNat := by
        rw [b0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hwa2 : s'.mem.accessible ((s.regs 4).toNat - 136) (136 + 32) true = true := by
        rw [bfr.accessible]
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact hwa
      have hcap2 : (s.regs 3).toNat + decLen (s.regs 7).toNat ≤ (s.regs 1).toNat := hcap
      have hmaskall : ∀ j, j < 24 → j &&& ((BitVec.ofNat 64 j - 24#64).sshiftRight 63).toNat = j := by decide
      have hmask := hmaskall (24 - decLen (s.regs 7).toNat) (by omega)
      janus64_run [hmask] calls [memmove_sum]
      rename_i a0 hrip2 hr4 hx2 hdf2 hmx2 hdl2 hrg2 hby2 hfr2
      have hdig3 : ∀ k, k < decLen (s.regs 7).toNat → s'.mem.readLE ((s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat - 1 - k) 1 = 48 + (s.regs 7).toNat / 10 ^ k % 10 := by
        intro k hk
        have hnd := hby2 (decLen (s.regs 7).toNat - 1 - k) (by omega)
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hnd
        rw [show (s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat - 1 - k = (s.regs 0).toNat + (s.regs 3).toNat + (decLen (s.regs 7).toNat - 1 - k) by omega, hnd,
          show (s.regs 4).toNat - 120 + (24 - decLen (s.regs 7).toNat) + 48 + (decLen (s.regs 7).toNat - 1 - k) = (s.regs 4).toNat - 72 + 23 - k by omega]
        exact bdig2 k hk
      refine ⟨?_, ?_, ?_, hdig3, ?_, ?_⟩
      · omega
      · have := hrg2 14 (by simp)
        simpa [b14] using this
      · rw [hx2 15 (by omega), bx]
      · have tr : ∀ {m1 m2 m3 : Memory}, MemFrame m1 m2 [((s.regs 0).toNat + (s.regs 3).toNat,
            (s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat), ((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)] →
            MemFrame m2 m3 [((s.regs 0).toNat + (s.regs 3).toNat,
            (s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat), ((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)] →
            MemFrame m1 m3 [((s.regs 0).toNat + (s.regs 3).toNat,
            (s.regs 0).toNat + (s.regs 3).toNat + decLen (s.regs 7).toNat), ((s.regs 4).toNat - 0x88, (s.regs 4).toNat + 0x20)] :=
          fun h h' => h.trans h' (fun a n h => ⟨h, h⟩)
        refine tr ?_ (tr (bfr.mono ?_) (tr ?_ (hfr2.mono ?_)))
        · repeat' first
            | exact MemFrame.refl _ _
            | refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by omega) (by omega)
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
        · repeat' first
            | exact MemFrame.refl _ _
            | refine MemFrame.writeLE ?_ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (by omega) (by omega)
        · intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
      · refine hdl2 ?_
        repeat' first
          | exact bdl
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwa2 (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hwa2 (Or.inr rfl) (by omega) (by omega)
          | refine TabsOK.writeLE ?_ ?_ _
end Fv256.Amd64.Dec
