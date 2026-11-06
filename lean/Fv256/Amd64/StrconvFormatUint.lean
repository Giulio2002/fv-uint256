import Fv256.DecProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecT
import Fv256.Amd64.DecM
import Fv256.DecAt
import Fv256.GrabTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev fu : Nat := segAddr Fv256.DecProg.program "internal/strconv.FormatUint"
abbrev ssAddrL : Nat := Fv256.DecProg.program.contractAddr "runtime.slicebytetostring"

theorem tabs_frame_out {M M' : Memory} (h : TabsOK M) {rs : List (Nat × Nat)} (hf : MemFrame M M' rs)
    (h1 : Outside 5163273 256 rs) (h2 : Outside 5176582 256 rs) : TabsOK M' := by
  refine TabsOK.intro (by rw [hf.accessible]; exact h.acc1) (by rw [hf.accessible]; exact h.acc2) (fun d hd => ?_) (fun d hd => ?_)
    (fun a n hw' => ?_)
  · rw [hf.readLE _ _ (Outside.of_sub h1 (by omega) (by omega))]; exact h.dig d hd
  · rw [hf.readLE _ _ (Outside.of_sub h2 (by omega) (by omega)), hf.readLE _ _ (Outside.of_sub h2 (by omega) (by omega))]
    exact h.smalls d hd
  · rw [hf.accessible] at hw'; exact h.ap _ _ hw'

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem formatUint_summary (st : Nat) (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (hc : RtContract64 (Fv256.DecProg.program.link impl) ssAddrL rt 4096 H (slicebytetostringSpec st)) :
    Summary (Fv256.DecProg.program.link impl) fu
      (fun s => s.regs 3 = 10#64 ∧ (s.regs 0).toNat < 2 ^ 64 ∧ StackGuardOK s 0 ∧ StackWritable s (0x58 + 4096) 8 ∧
        (s.regs 4).toNat % 8 = 0 ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ TabsOK s.mem ∧
        Outside ((s.regs 4).toNat - 0x58 - 4096) (4096 + 0x58 + 8) rt ∧
        Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (100 ≤ (s.regs 0).toNat → H [0, (s.regs 4).toNat - 0x20 + (24 - decLen (s.regs 0).toNat), decLen (s.regs 0).toNat]
          (s.regs 14).toNat ((s.regs 4).toNat - 0x58) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (s.regs 0).toNat) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) ∧ TabsOK s'.mem ∧
        DecAt rt 5163273 5176582 5134938 (s'.regs 0).toNat (s'.regs 3).toNat) := by
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
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_, ?_⟩
      · rw [decBytes_lt _ h10]; rfl
      · exact accessible_sub htab.acc1 (Or.inl rfl) (by omega) (by omega)
      · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      · exact htab.writeLE (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _
      · simp only [DecAt]; right; left; constructor <;> simp [setRegF] <;> omega
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
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_, ?_⟩
      · rw [decBytes_ge _ (by omega), decBytes_lt _ (by omega)]; simp
      · exact accessible_sub htab.acc2 (Or.inl rfl) (by omega) (by omega)
      · exact (MemFrame.refl s.mem _).writeLE _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      · exact htab.writeLE (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _
      · simp only [DecAt]; right; right; left; constructor <;> simp [setRegF] <;> omega
  · have hge : 100 ≤ (s.regs 0).toNat := by omega
    have hdl20 := decLen_le_20 _ hu
    have hsp := (s.regs 4).isLt
    janus64_run [hb10] until [4227552]
    refine ReachesRet.call_regions fb ?_ ?_ ?_
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
    · intro sA hrip ⟨b0, b4, b5, b14, bx, bdf, bmx, bdig, bfr, btab⟩ hrgA
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
      have hfs : MemFrame s.mem sA.mem [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)] := by
        refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) ?_ bfr ?_
        · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) ?_ ?_)
          all_goals (dsimp only; omega)
        · intro a n h
          refine ⟨h, ?_⟩
          simp only [outside_cons] at h ⊢
          refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
      have hrtv : rtView rt sA.mem = rtView rt s.mem := by
        refine Janus.Contracts.Stack.rtView_eq_of_frame hfs ?_ ?_
        · simpa using hrgA
        · intro a ha
          obtain ⟨r, hr, h1, h2⟩ := ha
          have := MemFrame.outside_mem hrt1 hr
          simp only [outside_cons]
          exact ⟨by omega, trivial⟩
      have hacc3 : 0 < 18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat)) →
          Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 80 + (24 - decLen (s.regs 0).toNat) + 48)
            (18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat))) false = true :=
        fun _ => accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      have hH3 : H [0, (s.regs 4).toNat - 80 + (24 - decLen (s.regs 0).toNat) + 48,
          18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat))]
          (s.regs 14).toNat ((s.regs 4).toNat - 88) (rtView rt sA.mem) := by
        rw [hrtv]
        have e1 : (s.regs 4).toNat - 80 + (24 - decLen (s.regs 0).toNat) + 48 = (s.regs 4).toNat - 0x20 + (24 - decLen (s.regs 0).toNat) := by omega
        have e2 : 18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat)) = decLen (s.regs 0).toNat := by omega
        rw [e1, e2]; exact hH2
      have hF : False → Spec.Disjoint ((s.regs 4).toNat - 80 + (24 - decLen (s.regs 0).toNat) + 48)
          (18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat))) 0 32 := fun h => h.elim
      janus64_run [hmask, hmask2] calls [hc]
      grab_const Janus.Contracts.StrAt as hright
      grab_last_const Janus.MemFrame as hleft
      obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
      have eL : 18446744073709551616 - (18446744073709551592 + (24 - decLen (s.regs 0).toNat)) = decLen (s.regs 0).toNat := by omega
      have eA : (s.regs 4).toNat - 80 + (24 - decLen (s.regs 0).toNat) + 48 = (s.regs 4).toNat - 32 + (24 - decLen (s.regs 0).toNat) := by omega
      rw [eL, eA] at hr1 hr4
      have hdig : strBytes sA.mem ((s.regs 4).toNat - 32 + (24 - decLen (s.regs 0).toNat)) (decLen (s.regs 0).toNat) = decBytes (s.regs 0).toNat :=
        strBytes_dec _ _ _ (fun k hk => by
          have := bdig k hk
          rw [← Janus.Arm64.Memory.readLE_one] at this
          have e : (s.regs 4).toNat - 32 + (24 - decLen (s.regs 0).toNat) + decLen (s.regs 0).toNat - 1 - k = (s.regs 4).toNat - 32 + 23 - k := by omega
          rw [e]; exact this)
      have hap := htab.apart hwa
      refine ⟨⟨?_, hr2, hr3, ?_⟩, ?_, ?_, ?_⟩
      · rw [hr1, hdig]
      · rw [hr4]; exact hdig
      · have hfs' : MemFrame s.mem sA.mem (rt ++ [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) :=
          hfs.mono (fun a n h => by simp only [outside_append] at h; exact h.2)
        have h1 : MemFrame sA.mem (Arm64.Memory.writeLE sA.mem ((s.regs 4).toNat - 88) 8 4225542)
            (rt ++ [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) :=
          MemFrame.of_writeLE sA.mem 4225542 (List.mem_append_right _ (List.mem_singleton_self _)) (by dsimp only; omega) (by dsimp only; omega)
        have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 0x58 - 4096, (s.regs 4).toNat)]) hleft (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          refine ⟨h.1, ?_, ?_, trivial⟩ <;> omega)
        exact hfs'.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
      · have hacc : sA.mem.accessible ((s.regs 4).toNat - 88) 8 true = true := by
          rw [hfs.accessible]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
        refine tabs_frame_out (btab.writeLE hacc 4225542) hleft ?_ ?_
        · simp only [outside_append, outside_cons]
          refine ⟨hrt2, ?_, ?_, trivial⟩ <;> omega
        · simp only [outside_append, outside_cons]
          refine ⟨hrt3, ?_, ?_, trivial⟩ <;> omega
      · simp only [DecAt]; left
        simp only [slicebytetostringSpec, argWords64, wordsFrom, arg, List.getD_eq_getElem?_getD, StrAt] at hat
        have hlen := hr1
        simp only [Spec.strBytes, List.length_map, List.length_range] at hlen
        have h3 : 3 ≤ decLen (s.regs 0).toNat := by
          rw [decLen_ge _ (by omega), decLen_ge _ (by omega)]
          have := decLen_pos ((s.regs 0).toNat / 10 / 10); omega
        rcases hat with h | h | h | h
        · omega
        · omega
        · omega
        · exact h.2.2
end Fv256.Amd64.Dec
