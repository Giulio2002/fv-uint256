import Fv256.Amd64.DecSummary
import Fv256.Amd64.StrconvFormatUintGen

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem dec_summary_gen (st : Nat) (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (G : Nat → Nat → Memory → Prop) (hG : ∀ r0 r1 m m', rtView rt m = rtView rt m' → G r0 r1 m → G r0 r1 m')
    (hc : RtContract64 (Fv256.DecProg.program.link impl) ssAddrL rt 4096 H (Fv256.Arm64.SbtsG.sbtsG st G)) :
    Summary (Fv256.DecProg.program.link impl) decE
      (fun s => s.regs 0 = z ∧ StackGuardOK s 4568 ∧ StackWritable s 4568 8 ∧ Fv256.DecProg.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4568) (4568 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 384 - 0x58) (rtView rt s.mem)) ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 140737488355328)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) ∧
        DecAt rt 5163273 5176582 5134938 (s'.regs 0).toNat (s'.regs 3).toNat ∧
        (valueAt s z 32 < 100 → MemFrame s.mem s'.mem [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) ∧
        (100 ≤ valueAt s z 32 → G (s'.regs 0).toNat (s'.regs 3).toNat s'.mem)) := by
  intro s hpc0 ⟨hz0r, hg, hw, hd, hout, hrt1, hrt2, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1, hxx, hdf0, hret47⟩
  have hg_ : StackGuardOK s 0xf8 := ⟨hg.noWrap, hg.readable, by have := hg.below; omega⟩
  have hw_ : StackWritable s 0x318 0x8 := ⟨by have := hw.1; omega, by have := hw.2.1; omega,
    by have := hw.2.2; exact accessible_sub this (Or.inr rfl) (by omega) (by omega)⟩
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hdE : decE = 4931168 := by unfold decE; decide
  have hrip : AtEntry s := by unfold AtEntry; exact hpc0
  clear hpc0
  have hl0 := Janus.Arm64.Memory.readLE_lt s.mem z.toNat 8
  have hl1 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 8) 8
  have hl2 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 16) 8
  have hl3 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 24) 8
  simp only [Nat.reducePow] at hl0 hl1 hl2 hl3
  have hv32 := Util.readLE_32 s.mem z.toNat
  obtain ⟨v, hvd⟩ : ∃ v, s.mem.readLE z.toNat 32 = v := ⟨_, rfl⟩
  have hvl : v = s.mem.readLE z.toNat 8 + 2 ^ 64 * s.mem.readLE (z.toNat + 8) 8 + 2 ^ 128 * s.mem.readLE (z.toNat + 16) 8 +
      2 ^ 192 * s.mem.readLE (z.toNat + 24) 8 ∧ True := ⟨by rw [← hvd, hv32], trivial⟩
  have hvlt : v < 2 ^ 256 := by rw [← hvd]; simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  rw [hvd] at hH hH1
  clear hv32
  by_cases hbig : 2 ^ 64 ≤ v
  · -- the number does not fit in 64 bits
    have hH2 := hH hbig
    have hnb : s.mem.readLE (z.toNat + 8) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 16) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 24) 8 ≠ 0 := by
      refine Decidable.byContradiction fun hcon => ?_
      simp only [not_or, Decidable.not_not] at hcon
      omega
    have hr4 := (s.regs 4).isLt
    have hx15 : s.xmm 15 = 0 := hxx
    have e0z : s.regs 0 = z := hz0r
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [e0z]; simp
    refine Fv256.E.reachesRet_bind' (Fv256.E.reachesRet_link impl
      (dec_init s hrip.rip z.toNat e0 hg_ hw_ hal hd ⟨hzn, hza⟩ (by omega) hnb hx15).regions) ?_
    intro S hrS ⟨⟨h0, h1, h2, h4, h5, h7, h9, h14, hx, hdf, hfr, hwy, hwd, hzero, htabS, hbpS⟩, hregS⟩
    have hbb : 0x1a0 ≤ (s.regs 4).toNat - 0x178 := by omega
    have hwb2 : S.mem.accessible ((s.regs 4).toNat - 0x178 - 0x1a0) (0x1a0 + 0x180) true = true := by
      rw [hfr.accessible]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    have hwy' : Fv256.B.wv S.mem ((s.regs 4).toNat - 0x178 + 280) 4 = v := by
      rw [hwy, Fv256.B.wv4_eq, hvd]
    have hg3S : S.mem.readLE ((s.regs 14).toNat + 16) 8 + 0x200 < (s.regs 4).toNat - 0x178 := by
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; omega
    have hg2S : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hfr.accessible]; exact hg2
    have hbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := hbpS
    have hrtv1 : rtView rt S.mem = rtView rt s.mem := by
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [((s.regs 4).toNat - 0x178 - 0x1a0, (s.regs 4).toNat)]) hfr hregS ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, trivial⟩
    refine Fv256.E.reachesRet_bind' (Fv256.E.reachesRet_link impl
      (dec_loop ((s.regs 4).toNat - 0x178) v (s.regs 14).toNat S.mem hbig hvlt hbb
        (by omega) (by omega) hwb2 hg3S (by omega) hg2S (by omega) v 0 S
        (by simp) (by omega) hrS (by simpa using h0) h1 (by simpa using h2) h4 h5 h7 h9
        (by rw [h14]; simp) hx (hdf.trans hdf0) (MemFrame.refl _ _) hwy' hwd (fun k hk => by omega) (by simpa using hzero) htabS).regions) ?_
    intro S2 hrS2 ⟨⟨q2, q13, q4, q5, q14, qx, qdf, qfr, qdig, qtab⟩, hregS2⟩
    have hrtv : rtView rt S2.mem = rtView rt s.mem := by
      rw [← hrtv1]
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [((s.regs 4).toNat - 0x178 - 0x1a0, (s.regs 4).toNat - 0x178 + 368)]) qfr
        hregS2 ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, trivial⟩
    have hrip2 : S2.rip = BitVec.ofNat 64 decX := hrS2
    have hdl20 : decLen v ≤ 78 := decLen_le_of_lt_pow v 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
    have hdl1 := decLen_pos v
    have hdlm : decLen v % 18446744073709551616 = decLen v := Nat.mod_eq_of_lt (by omega)
    have hX1 : 4096 ≤ (s.regs 4).toNat - 376 - 8 := by omega
    have hX2 : s.mem.accessible ((s.regs 4).toNat - 376 - 8 - 4096) 4128 true = true :=
      accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    have hX3 : s.mem.accessible ((s.regs 4).toNat - 376 + 86 + (98 - decLen v)) (decLen v) false = true :=
      accessible_sub hwa (Or.inl rfl) (by omega) (by omega)
    have hX4 : H [0, (s.regs 4).toNat - 376 + 86 + (98 - decLen v), decLen v] (s.regs 14).toNat
        ((s.regs 4).toNat - 376 - 8) (rtView rt S2.mem) := by rw [hrtv]; exact hH2
    have hX3' : 0 < decLen v → s.mem.accessible ((s.regs 4).toNat - 376 + 86 + (98 - decLen v)) (decLen v) false = true := fun _ => hX3
    have hX6 : False → Spec.Disjoint ((s.regs 4).toNat - 376 + 86 + (98 - decLen v)) (decLen v) 0 32 := fun h => h.elim
    have hX9 : s.mem.readLE ((s.regs 4).toNat - 376 + 376) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [show (s.regs 4).toNat - 376 + 376 = (s.regs 4).toNat by omega]
    have hX7 : s.mem.readLE ((s.regs 4).toNat - 376 + 376) 8 < 140737488355328 := by
      rw [hX9]; exact hret47
    have hX5 : (s.regs 4).toNat - 376 + 86 + (98 - decLen v) + decLen v ≤ 281474976710656 := by omega
    janus64_run [hdE, q2, q13, q4, q5, q14, hdlm, hX9] calls [hc]
    grab_const Janus.Contracts.StrAt as hright
    grab_frame 4096 as hleft
    obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
    have hGc := ‹G _ _ _›
    have hdig : Spec.strBytes S2.mem ((s.regs 4).toNat - 376 + 86 + (98 - decLen v)) (decLen v) = decBytes v :=
      strBytes_dec _ _ _ (fun k hk => by
        have := qdig k hk
        rw [show (s.regs 4).toNat - 376 + 86 + (98 - decLen v) + decLen v - 1 - k = (s.regs 4).toNat - 376 + 86 + 97 - k by omega]
        exact this)
    refine ⟨⟨?_, hr2, hr3, ?_⟩, ?_, ?_, ?_⟩
    · rw [hr1, hdig]; simp [valueAt, hvd]
    · rw [hr4, hdig, valueAt, hvd]
    · have hx := (s.regs 4).isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show (s.regs 4).toNat - 376 + 368 = (s.regs 4).toNat - 8 by omega, hbp]
      simp
    · have h1 : MemFrame s.mem S.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        hfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h2 : MemFrame S.mem S2.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        qfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h3 : MemFrame S2.mem (Arm64.Memory.writeLE S2.mem ((s.regs 4).toNat - 376 - 8) 8 4931926)
          (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        MemFrame.of_writeLE S2.mem 4931926 (List.mem_append_right _ (List.mem_singleton_self _)) (by simp; omega) (by simp; omega)
      have h4 : MemFrame (Arm64.Memory.writeLE S2.mem ((s.regs 4).toNat - 376 - 8) 8 4931926) _
          (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        hleft.mono (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, by omega, trivial⟩)
      refine ⟨h1.trans (h2.trans (h3.trans h4 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩, ?_, fun h => absurd h (by simp only [valueAt]; omega), fun _ => hGc⟩
      simp only [DecAt]; left
      simp only [slicebytetostringSpec, argWords64, wordsFrom, arg, List.getD_eq_getElem?_getD, StrAt] at hat
      have hlen := hr1
      simp only [Spec.strBytes, List.length_map, List.length_range] at hlen
      have h3' : 2 ≤ decLen v := by
        rw [decLen_ge _ (by omega), decLen_ge _ (by omega)]
        have := decLen_pos (v / 10 / 10); omega
      rcases hat with h | h | h | h
      · omega
      · omega
      · omega
      · exact h.2.2
  · by_cases hz0 : v = 0
    · have hl0 : s.mem.readLE z.toNat 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hzs := zeroStr_read hd
      have hzv : valueAt s z 32 = 0 := by simp only [valueAt]; rw [hvd]; exact hz0
      have hdj := dataLoaded_disjoint hd zeroDat_mem hwa
      rw [zeroDat_base, zeroDat_len] at hdj
      janus64_run [hdE, hrip.rip, hl0, hl1', hl2', hl3']
      rw [hzv]
      refine ⟨⟨by simp [decBytes_lt 0 (by omega)], hzs.2, ?_⟩, ?_, ?_, fun _ => ?_, fun h => absurd h (by first | (simp only [valueAt]; omega) | omega)⟩
      · simp only [decBytes_lt 0 (by omega), Spec.strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
      · exact MemFrame.of_writeLE s.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      · simp only [DecAt]; right; right; right; constructor <;> simp [setRegF] <;> omega
      · exact MemFrame.of_writeLE s.mem _ (List.mem_singleton_self _) (by omega) (by omega)
    · have hlow : s.mem.readLE (z.toNat + 8) 8 = 0 ∧ s.mem.readLE (z.toNat + 16) 8 = 0 ∧ s.mem.readLE (z.toNat + 24) 8 = 0 := by
        have := hvl.1
        omega
      have hl0 : s.mem.readLE z.toNat 8 = v := by have := hvl.1; omega
      have hv64 : v < 2 ^ 64 := by omega
      have hfu := formatUint_summary_gen st impl rt H G hG hc
      have hdl20 := decLen_le_20 v hv64
      have hdl1 := decLen_pos v
      have hHf : 100 ≤ v → H [0, (s.regs 4).toNat - 384 - 32 + (24 - decLen v), decLen v] (s.regs 14).toNat
          ((s.regs 4).toNat - 384 - 88) (rtView rt s.mem) := fun h => hH1 h hv64
      have hT : TabsOK ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
          ((s.regs 4).toNat - 384) 8 4931476) := by
        refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.of_loaded hd) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _) ?_ _
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      have hzv : valueAt s z 32 = v := by simp only [valueAt]; exact hvd
      have hnzv : ((BitVec.ofNat 64 v ||| 0#64 ||| 0#64 ||| 0#64).toNat = 0) = False := by
        apply eq_false
        intro h
        simp only [BitVec.or_zero, BitVec.toNat_ofNat] at h
        omega
      janus64_run [hdE, hrip.rip, hlow.1, hlow.2.1, hlow.2.2, hl0, hnzv] calls [hfu]
      clear hfu
      grab_last_const Janus.MemFrame as hqimp
      grab_const Fv256.E.DecAt as hqd
      grab_const Fv256.E.decBytes as hqs
      grab_const Janus.MemFrame as hqf
      rw [hzv]
      obtain ⟨q1, q2, q3, q4⟩ := hqs
      refine ⟨⟨q1, q2, q3, q4⟩, ?_, hqd, fun hlt => ?_, fun h => ?_⟩
      · have h1 : MemFrame s.mem (((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
            ((s.regs 4).toNat - 384) 8 4931476)) (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) := by
          refine MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)])
            (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
            (MemFrame.of_writeLE _ _ (rs := rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
          intro a n h; exact ⟨h, h⟩
        have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) hqf (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, trivial⟩)
        exact h1.trans h2 fun a n h => ⟨h, h⟩
      · have h1w : MemFrame s.mem (((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
            ((s.regs 4).toNat - 384) 8 4931476)) [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)] := by
          refine MemFrame.trans (rs := [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)])
            (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)) (List.mem_singleton_self _) (by omega) (by omega))
            (MemFrame.of_writeLE _ _ (rs := [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)) (List.mem_singleton_self _) (by omega) (by omega)) ?_
          intro a n h; exact ⟨h, h⟩
        have hv100 : v < 100 := by simpa [valueAt, hvd] using hlt
        have h2w := MemFrame.mono (rs' := [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) (hqimp (by simpa using hv100)) (fun a n h => by
          simp only [outside_cons, outside_nil, Outside, and_true] at h ⊢
          omega)
        exact h1w.trans h2w fun a n h => ⟨h, h⟩
      · exact ‹100 ≤ _ → G _ _ _› (by simpa [valueAt, hvd] using h)

end Fv256.Amd64.Dec
