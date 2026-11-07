import Fv256.Arm64.DecProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.UtilE64
import Fv256.Arm64.DecT
import Fv256.DecAt
import Fv256.GrabTac
import Fv256.Arm64.DecA
import Fv256.Arm64.DecL

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

abbrev fu : Nat := segAddr Fv256.Arm64.DecProg.program "internal/strconv.FormatUint"
abbrev ssAddrL : Nat := Fv256.Arm64.DecProg.program.contractAddr "runtime.slicebytetostring"

theorem steps_link64 {p : Janus.Program} (impl : List Segment) {s s' : State} {k : Nat}
    (h : Janus.Program.Steps p s k s') : Janus.Program.Steps (p.link impl) s k s' := by
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    exact .step (by simpa using hx) (by simpa using hs) (Janus.Program.fetch_link impl hf) hst ih

/-- A summary of `p` is a summary of `p` linked with further code. -/
theorem summary_link64 {p : Janus.Program} (impl : List Segment) {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Summary p entry pre post) : Summary (p.link impl) entry pre post := by
  intro s hpc hp
  obtain ⟨k, s', hst, hr, hq⟩ := h s hpc hp
  exact ⟨k, s', steps_link64 impl hst, hr, hq⟩

theorem tabs_frame_out {M M' : Janus.Arm64.Memory} (h : TabsOK M) {rs : List (Nat × Nat)} (hf : MemFrame M M' rs)
    (h1 : Outside 989280 256 rs) (h2 : Outside 1002589 256 rs) : TabsOK M' := by
  refine TabsOK.intro (by rw [hf.accessible]; exact h.acc1) (by rw [hf.accessible]; exact h.acc2) (fun d hd => ?_) (fun d hd => ?_)
    (fun a n hw' => ?_)
  · rw [hf.readLE _ _ (Outside.of_sub h1 (by omega) (by omega))]; exact h.dig d hd
  · rw [hf.readLE _ _ (Outside.of_sub h2 (by omega) (by omega)), hf.readLE _ _ (Outside.of_sub h2 (by omega) (by omega))]
    exact h.smalls d hd
  · rw [hf.accessible] at hw'; exact h.ap _ _ hw'

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- Summary of `internal/strconv.FormatUint(u, 10)` (arm64): the result string holds the decimal digits of `u`. -/
theorem formatUint_summary (st : Nat) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (hc : RtContract (Fv256.Arm64.DecProg.program.link impl) ssAddrL rt 4096 H (slicebytetostringSpec st)) :
    Summary (Fv256.Arm64.DecProg.program.link impl) fu
      (fun s => s.regs 1 = 10#64 ∧ GuardOK s 96 ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4192 ∨ s.sp.toNat ≤ (s.regs 28).toNat + 16) ∧ s.sp.toNat % 16 = 0 ∧ 4192 ≤ s.sp.toNat ∧ s.sp.toNat < 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 4192) 4192 true = true ∧ TabsOK s.mem ∧
        Outside (s.sp.toNat - 4192) 4192 rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0 ∧
        (100 ≤ (s.regs 0).toNat → H [0, s.sp.toNat - 32 + (24 - decLen (s.regs 0).toNat), decLen (s.regs 0).toNat]
          (s.regs 28).toNat (s.sp.toNat - 96) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (s.regs 0).toNat) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 8)]) ∧ TabsOK s'.mem ∧
        DecAt rt 989280 1002589 960826 (s'.regs 0).toNat (s'.regs 1).toNat ∧
        ((s.regs 0).toNat < 100 → MemFrame s.mem s'.mem [(s.sp.toNat - 4192, s.sp.toNat - 8)])) := by
  intro s hpc ⟨hb10, hg, hgd, hal, h4192, hsp2, hw, htab, hrt1, hrt2, hrt3, hret, hret4, hH⟩
  have hc2 : fu + 0x300 < 2 ^ 47 := by decide
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hu := (s.regs 0).isLt
  have hs := s.sp.isLt
  rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
  tabs_data htab [hw]
  by_cases h100 : (s.regs 0).toNat < 100
  · have hsr := htab.sm (s.regs 0).toNat h100
    by_cases h10 : (s.regs 0).toNat < 10
    · have hl : decLen (s.regs 0).toNat = 1 := decLen_lt _ h10
      janus_run [hb10]
      have hd0 := htab.dig (s.regs 0).toNat h10
      have hsb : strBytes s.mem (989280 + (s.regs 0).toNat) 1 = decBytes (s.regs 0).toNat := by
        rw [decBytes_lt _ h10]
        simp only [strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [← Janus.Arm64.Memory.readLE_one, Nat.add_zero, hd0]
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_, ?_, ?_⟩
      · rw [decBytes_lt _ h10]; rfl
      · exact accessible_sub htab.acc1 (Or.inl rfl) (by omega) (by omega)
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine MemFrame.writeLE ?_ _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
      · repeat' first
          | exact htab
          | refine TabsOK.writeLE ?_ ?_ _
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
      · simp only [DecAt]; right; left; constructor <;> simp [setReg] <;> omega
      · intro _
        repeat' first
          | exact MemFrame.refl _ _
          | (refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega))
    · have hl : decLen (s.regs 0).toNat = 2 := by
        rw [decLen_ge _ (by omega), decLen_lt _ (by omega)]
      janus_run [hb10]
      have hsb : strBytes s.mem (1002589 + 2 * (s.regs 0).toNat) 2 = decBytes (s.regs 0).toNat := by
        rw [decBytes_ge _ (by omega), decBytes_lt _ (by omega)]
        have e : strBytes s.mem (1002589 + 2 * (s.regs 0).toNat) 2 =
            [(s.mem.bytes (1002589 + 2 * (s.regs 0).toNat)).toNat, (s.mem.bytes (1002589 + 2 * (s.regs 0).toNat + 1)).toNat] := by
          simp [strBytes, List.range_succ]
        rw [e, ← Janus.Arm64.Memory.readLE_one, ← Janus.Arm64.Memory.readLE_one, hsr.1, hsr.2]
        simp only [List.cons_append, List.nil_append]
        try omega
      refine ⟨⟨?_, by omega, ?_, hsb⟩, ?_, ?_, ?_, ?_⟩
      · rw [decBytes_ge _ (by omega), decBytes_lt _ (by omega)]; simp
      · exact accessible_sub htab.acc2 (Or.inl rfl) (by omega) (by omega)
      · repeat' first
          | exact MemFrame.refl _ _
          | (refine MemFrame.writeLE ?_ _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
      · repeat' first
          | exact htab
          | refine TabsOK.writeLE ?_ ?_ _
          | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact accessible_sub hw (Or.inr rfl) (by omega) (by omega))
          | exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
      · simp only [DecAt]; right; right; left; constructor <;> simp [setReg] <;> omega
      · intro _
        repeat' first
          | exact MemFrame.refl _ _
          | (refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega))
  · have hge : 100 ≤ (s.regs 0).toNat := by omega
    have hdl20 := decLen_le_20 _ hu
    have hnd1 := decLen_pos (s.regs 0).toNat
    have fbs := summary_link64 impl fb10_summary
    have h96 := toNat_sub_lit s.sp 96 (by omega)
    have h104 := toNat_sub_lit s.sp 104 (by omega)
    janus_run [hb10] until [94000]
    refine ReachesRet.call_regions fbs ?_ ?_ ?_
    · rfl
    · have h32 := toNat_sub_lit s.sp 32 (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [GuardOK, setReg, Janus.Arm64.Memory.accessible_writeLE]
        refine ⟨by omega, hg2, ?_⟩
        repeat rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        omega
      · rw [h96]; omega
      · rw [h96]; omega
      · rw [h96]; omega
      · try dsimp only
        simp only [Janus.Arm64.Memory.accessible_writeLE, h96]
        exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
      · simp [setReg, h32]; omega
      · simp [setReg, h32, Janus.Arm64.Memory.accessible_writeLE]
        exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
      · simp [setReg]; omega
      · simp [setReg, h32, h96]; omega
      · try dsimp only
        repeat' first | exact htab | refine TabsOK.writeLE ?_ ?_ _
        all_goals (try simp only [Janus.Arm64.Memory.accessible_writeLE])
        all_goals (exact accessible_sub hw (Or.inr rfl) (by omega) (by omega))
      · simp [setReg]
        try omega
      · simp [setReg]
        try omega
    · intro sA hrip ⟨b0, bsp, b29, bk, bdig, bfr, btab⟩ hrgA
      simp [setReg] at b0 bsp b29 bk bdig bfr
      have e32 : (18446744073709551584 + s.sp.toNat) % 18446744073709551616 = s.sp.toNat - 32 := by omega
      have e96 : (18446744073709551520 + s.sp.toNat) % 18446744073709551616 = s.sp.toNat - 96 := by omega
      simp only [e32, e96] at bdig bfr
      have hmask := (by decide : ∀ j, j < 24 → ((BitVec.ofNat 64 j - 24#64).sshiftRight 63).toNat &&& j = j) (24 - decLen (s.regs 0).toNat) (by omega)
      have hmask2 : (24 - decLen (s.regs 0).toNat) &&& ((BitVec.ofNat 64 (24 - decLen (s.regs 0).toNat) - 24#64).sshiftRight 63).toNat = 24 - decLen (s.regs 0).toNat := by
        rw [Nat.and_comm]; exact hmask
      have hH2 := hH hge
      have hfs : MemFrame s.mem sA.mem [(s.sp.toNat - 4192, s.sp.toNat - 8)] := by
        refine MemFrame.trans (rs := [(s.sp.toNat - 4192, s.sp.toNat - 8)]) ?_ bfr ?_
        · repeat' first
            | exact MemFrame.refl _ _
            | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) ?_ ?_
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
      rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]] at *
      have h28 : sA.regs 28 = s.regs 28 := by
        have := bk 28 (by simp [Clob])
        simpa [setReg] using this
      have hacc3 : 0 < 18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592 →
          s.mem.accessible (24 - decLen (s.regs 0).toNat + (s.sp.toNat - 32))
            (18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592) false = true :=
        fun _ => accessible_sub hw (Or.inr rfl) (by omega) (by omega)
      have hF : False → Disjoint (24 - decLen (s.regs 0).toNat + (s.sp.toNat - 32))
          (18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592) 0 32 := fun h => h.elim
      have hH3 : H [0, 24 - decLen (s.regs 0).toNat + (s.sp.toNat - 32),
          18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592]
          (s.regs 28).toNat (s.sp.toNat - 96) (rtView rt sA.mem) := by
        rw [hrtv]
        have e1 : 24 - decLen (s.regs 0).toNat + (s.sp.toNat - 32) = s.sp.toNat - 32 + (24 - decLen (s.regs 0).toNat) := by omega
        have e2 : 18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592 = decLen (s.regs 0).toNat := by omega
        rw [e1, e2]; exact hH2
      janus_run [hmask, hmask2] calls [hc]
      grab_const Janus.Contracts.StrAt as hright
      grab_last_const Janus.MemFrame as hleft
      obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
      have eL : 18446744073709551616 - (24 - decLen (s.regs 0).toNat) - 18446744073709551592 = decLen (s.regs 0).toNat := by omega
      have eA : 24 - decLen (s.regs 0).toNat + (s.sp.toNat - 32) = s.sp.toNat - 32 + (24 - decLen (s.regs 0).toNat) := by omega
      rw [eL, eA] at hr1 hr4
      have hdig : strBytes sA.mem (s.sp.toNat - 32 + (24 - decLen (s.regs 0).toNat)) (decLen (s.regs 0).toNat) = decBytes (s.regs 0).toNat :=
        strBytes_dec _ _ _ (fun k hk => by
          have := bdig k hk
          rw [← Janus.Arm64.Memory.readLE_one] at this
          have e : s.sp.toNat - 32 + (24 - decLen (s.regs 0).toNat) + decLen (s.regs 0).toNat - 1 - k = s.sp.toNat - 32 + 23 - k := by omega
          rw [e]; exact this)
      have hap := htab.apart hw
      have hs18 : sA.regs 18 = s.regs 18 := by simpa [setReg] using bk 18 (by simp [Clob])
      refine ⟨⟨?_, hr2, hr3, ?_⟩, hs18, ?_, ?_, ?_, fun h => absurd h (by omega)⟩
      · rw [hr1, hdig]
      · rw [hr4]; exact hdig
      · have hfs' : MemFrame s.mem sA.mem (rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 8)]) :=
          hfs.mono (fun a n h => by simp only [outside_append] at h; exact h.2)
        have hl' := MemFrame.mono (rs' := rt ++ [(s.sp.toNat - 4192, s.sp.toNat - 8)]) hleft (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          refine ⟨h.1, ?_, ?_, trivial⟩ <;> omega)
        exact hfs'.trans hl' fun a n h => ⟨h, h⟩
      · refine tabs_frame_out btab hleft ?_ ?_
        · simp only [outside_append, outside_cons]
          refine ⟨hrt2, ?_, ?_, trivial⟩ <;> omega
        · simp only [outside_append, outside_cons]
          refine ⟨hrt3, ?_, ?_, trivial⟩ <;> omega
      · simp only [DecAt]; left
        simp only [slicebytetostringSpec, argWords, wordsFrom, arg, List.getD_eq_getElem?_getD, StrAt] at hat
        have h3 : 3 ≤ decLen (s.regs 0).toNat := by
          have h := decLen_div_pow (s.regs 0).toNat 2 (by show 100 ≤ (s.regs 0).toNat; omega)
          have h' := decLen_pos ((s.regs 0).toNat / 10 ^ 2)
          omega
        have hlen := hr1
        simp only [strBytes, List.length_map, List.length_range] at hlen
        rcases hat with h | h | h | h <;> first | exact h.2.2 | (exfalso; omega)
end Fv256.Arm64.Dec
