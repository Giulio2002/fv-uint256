import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecT
import Fv256.Amd64.DecM

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev fu : Nat := segAddr Extracted.program "internal/strconv.FormatUint"
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem formatUint_summary (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H slicebytetostringSpec) :
    Summary (Extracted.program.link impl) fu
      (fun s => s.regs 3 = 10#64 ∧ (s.regs 0).toNat < 2 ^ 64 ∧ StackGuardOK s 0 ∧ StackWritable s (0x58 + 4096) 8 ∧
        (s.regs 4).toNat % 8 = 0 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ TabsOK s.mem ∧
        Outside ((s.regs 4).toNat - 0x58 - 4096) (4096 + 0x58 + 8) rt ∧
        Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (100 ≤ (s.regs 0).toNat → H [0, (s.regs 4).toNat - 0x20 + (24 - decLen (s.regs 0).toNat), decLen (s.regs 0).toNat]
          (s.regs 14).toNat ((s.regs 4).toNat - 0x58) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (s.regs 0).toNat) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) ∧ TabsOK s'.mem) := by
  intro s hpc ⟨hb10, hu, hg, hw, hal, hret, htab, hrt1, hrt2, hrt3, hH⟩
  have hc2 : fu + 0x300 < 2 ^ 47 := by decide
  obtain ⟨hwb, hwn, hwa⟩ := hw
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hret hrt1 hH
  tabs_data htab [hwa]
  have fb := Fv256.E.summary_link impl fb10_summary
  by_cases h100 : (s.regs 0).toNat < 100
  · have hsr := htab.sm (s.regs 0).toNat h100
    by_cases h10 : (s.regs 0).toNat < 10
    · have hl : decLen (s.regs 0).toNat = 1 := decLen_lt _ h10
      janus64_run [hb10]
      have hd0 := htab.dig (s.regs 0).toNat h10
      have hsb : strBytes s.mem (5163273 + (s.regs 0).toNat) 1 = decBytes (s.regs 0).toNat := by
        rw [decBytes_lt _ h10]
        simp only [strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [← Janus.Arm64.Memory.readLE_one, Nat.add_zero, hd0]
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_⟩
      · rw [decBytes_lt _ h10]; rfl
      · exact accessible_sub htab.acc1 (Or.inl rfl) (by omega) (by omega)
      · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      · exact htab.writeLE (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _
    · have hl : decLen (s.regs 0).toNat = 2 := by
        rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
      janus64_run [hb10]
      have hsb : strBytes s.mem (5176582 + (s.regs 0).toNat * 2) 2 = decBytes (s.regs 0).toNat := by
        rw [decBytes_ge _ (by omega), decBytes_lt _ (by omega)]
        have e : strBytes s.mem (5176582 + (s.regs 0).toNat * 2) 2 =
            [(s.mem.bytes (5176582 + (s.regs 0).toNat * 2)).toNat, (s.mem.bytes (5176582 + (s.regs 0).toNat * 2 + 1)).toNat] := by
          simp [strBytes, List.range_succ]
        rw [e, ← Janus.Arm64.Memory.readLE_one, ← Janus.Arm64.Memory.readLE_one,
          show 5176582 + (s.regs 0).toNat * 2 = 5176582 + 2 * (s.regs 0).toNat by omega, hsr.1, hsr.2]
        simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
        try omega
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_⟩
      · rw [decBytes_ge _ (by omega), decBytes_lt _ (by omega)]; simp
      · exact accessible_sub htab.acc2 (Or.inl rfl) (by omega) (by omega)
      · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      · exact htab.writeLE (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _
  · have hge : 100 ≤ (s.regs 0).toNat := by omega
    have hdl20 := decLen_le_20 _ hu
    have hsp := (s.regs 4).isLt
    janus64_run [hb10] until [4227552]
    refine ReachesRet.call fb ?_ ?_ ?_
    · rfl
    · have h58 := toNat_sub_lit (s.regs 4) 0x58 (by omega)
      have h20 := toNat_sub_lit (s.regs 4) 0x20 (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try dsimp only)
      all_goals (try simp only [setRegF, Janus.Amd64.GoABI.regSP])
      all_goals (try (repeat' first | exact htab | refine TabsOK.writeLE ?_ ?_ _))
      all_goals (try simp only [Janus.Arm64.Memory.accessible_writeLE])
      all_goals (try simp [h58, h20])
      all_goals first
        | omega
        | exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
        | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega))
        | (rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide)
        | skip
    · intro sA hrip ⟨b0, b4, b5, b14, bx, bdf, bmx, bdig, bfr, btab⟩
      simp [setRegF] at b0 b4 b5 b14 bx bdig bfr
      have e32 : (18446744073709551584 + (s.regs 4).toNat) % 18446744073709551616 = (s.regs 4).toNat - 32 := by omega
      simp only [e32] at bfr bdig
      have hnd1 := decLen_pos (s.regs 0).toNat
      have hmask := (by decide : ∀ j, j < 24 → ((BitVec.ofNat 64 j - 24#64).sshiftRight 63).toNat &&& j = j) (24 - decLen (s.regs 0).toNat) (by omega)
      have hmask2 : (24 - decLen (s.regs 0).toNat) &&& ((BitVec.ofNat 64 (24 - decLen (s.regs 0).toNat) - 24#64).sshiftRight 63).toNat = 24 - decLen (s.regs 0).toNat := by
        rw [Nat.and_comm]; exact hmask
      have hb0' : (sA.regs 0).toNat = 24 - decLen (s.regs 0).toNat := by
        rw [b0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hH2 := hH hge
      janus64_run [hmask, hmask2] calls [hc]
      all_goals (try trace_state)
      all_goals sorry
end Fv256.Amd64.Dec
