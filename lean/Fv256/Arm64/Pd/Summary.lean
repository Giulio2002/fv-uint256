import Fv256.Arm64.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.PdCells
import Fv256.GrabTac
import Fv256.Arm64.P.T
import Fv256.Util
import Fv256.UtilB2
import Fv256.Arm64.Pd.Tabs
import Fv256.Arm64.Pd.Init
import Fv256.Arm64.Pd.Loop

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E Fv256.Arm64.P

namespace Fv256.Arm64.Pd

abbrev ssAddrL : Nat := Fv256.Arm64.PrettyProg.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem pdE_val : pdE = 755200 := by unfold pdE; decide
theorem pdF_val : pdF = 755764 := by unfold pdF; rw [pdE_val]

theorem steps_link64' {p : Janus.Program} (impl : List Segment) {s s' : State} {k : Nat}
    (h : Janus.Program.Steps p s k s') : Janus.Program.Steps (p.link impl) s k s' := by
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    exact .step (by simpa using hx) (by simpa using hs) (Janus.Program.fetch_link impl hf) hst ih

theorem pd_mask : ∀ c, c < 134 → 1 ≤ c →
    (132 - c + 1 &&& ((BitVec.ofNat 64 (132 - c) - 132#64).sshiftRight 63).toNat) = 132 - c + 1 := by decide

/-- A `ReachesRet` of the library program is one of the linked program. -/
theorem reachesRet64_link' {P : Janus.Program} (impl : List Segment) {t : W64} {s : State} {Q : State → Prop}
    (h : ReachesRet P t s Q) : ReachesRet (P.link impl) t s Q := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact ⟨k, s', steps_link64' impl hst, hr, hq⟩

set_option maxHeartbeats 600000 in
set_option maxRecDepth 200000 in
theorem pd_summary (st : Nat) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract (Fv256.Arm64.PrettyProg.program.link impl) ssAddrL rt 4096 H (slicebytetostringSpec st)) :
    Summary (Fv256.Arm64.PrettyProg.program.link impl) pdE
      (fun s => s.regs 0 = z ∧ s.regs 1 = sep ∧ GuardOK s 704 ∧ StackOK s 4608 24 ∧
        Fv256.Arm64.PrettyProg.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 24) rt ∧ Ptr32 s.mem z false ∧
        (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
        (s.mem.readLE z.toNat 32 ≠ 0 →
          H [0, s.sp.toNat - 168 - plen (s.mem.readLE z.toNat 32), plen (s.mem.readLE z.toNat 32)]
            (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt s.mem)) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (prettyBytes (sep.toNat % 256) (val256 s.mem z.toNat)) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])) := by
  intro s hpc ⟨hz0r, hsepr, hg, hst, hd, hout, ⟨hzn, hza⟩, hzd, hgd, hH, hr30, hr30a⟩
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4608, hsp2, hwa⟩ := hst
  have hcE : pdE + 0x5000 < 2 ^ 47 := by decide
  have hr := s.sp.isLt
  have hl0 := Janus.Arm64.Memory.readLE_lt s.mem z.toNat 8
  have hl1 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 8) 8
  have hl2 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 16) 8
  have hl3 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 24) 8
  simp only [Nat.reducePow] at hl0 hl1 hl2 hl3
  have hv32 := Util.readLE_32 s.mem z.toNat
  obtain ⟨v, hvd⟩ : ∃ v, s.mem.readLE z.toNat 32 = v := ⟨_, rfl⟩
  have hvlt : v < 2 ^ 256 := by rw [← hvd]; simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  rw [hvd] at hH
  simp only [val256, hvd]
  by_cases hz0 : v = 0
  · have hl0' : s.mem.readLE z.toNat 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hzs := zeroStr_read hd
    have hdj := dl_disjoint hd zeroDat_mem hwa
    rw [zeroDat_base, zeroDat_len] at hdj
    have hal2 : s.sp.toNat % 16 = 0 := hal
    janus_run [pdE_val, hpc, hal2, hl0', hl1', hl2', hl3', Nat.or_eq_zero_iff]
    rw [hz0, prettyBytes_lt _ _ (by omega), decBytes_lt 0 (by omega)]
    refine ⟨⟨by simp, hzs.2, ?_⟩, ?_⟩
    · simp only [Spec.strBytes, List.range_one, List.map_cons, List.map_nil]
      rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
    · refine MemFrame.trans (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])
        (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat - 8))
          (List.mem_append_right _ (List.mem_cons_self ..)) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])
          (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_append_right _ (List.mem_cons_self ..)) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
  · have hH2 := hH hz0
    have hnb : s.mem.readLE z.toNat 32 ≠ 0 := by rw [hvd]; exact hz0
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [hz0r]; simp
    have hg_ : GuardOK s 272 := ⟨hg1, hg2, by omega⟩
    have hb : 368 ≤ s.sp.toNat - 400 := by omega
    have hb16 : (s.sp.toNat - 400) % 16 = 0 := by omega
    have hb2 : s.sp.toNat - 400 + 424 ≤ 2 ^ 48 := by omega
    have hsb : (sep.toNat % 256) < 256 := Nat.mod_lt _ (by omega)
    refine Fv256.E.reachesRet64_bind (reachesRet64_link' impl
      (pd_init s hpc z.toNat e0 hg_ hal (by omega) (by omega) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) hd
        ⟨hza, hzn⟩ (by omega) hr30 hnb).regions) ?_
    intro S hrS ⟨⟨h0, h2, h3, h4, h6, h8, h29, hsp, hk, hfr, hsepS, hyS, hdS, hzeroS, htabS, hbpS, hretS⟩, hregS⟩
    have hrtv1 : rtView rt S.mem = rtView rt s.mem := by
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [(s.sp.toNat - 408, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)]) hfr hregS ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, by omega, trivial⟩
    have hk28 : S.regs 28 = s.regs 28 := hk 28 (by simp)
    have hwS : S.mem.accessible (s.sp.toNat - 400 - 368) (368 + 424) true = true := by
      rw [hfr.accessible]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    have hg3S : S.mem.readLE ((S.regs 28).toNat + 16) 8 + 304 < s.sp.toNat - 400 := by
      rw [hk28, hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; omega
    have hg2S : S.mem.accessible ((S.regs 28).toNat + 16) 8 false = true := by rw [hk28, hfr.accessible]; exact hg2
    have hg1S : (S.regs 28).toNat + 24 ≤ 2 ^ 48 := by rw [hk28]; exact hg1
    have hgdS : (S.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 400 - 368 ∨ s.sp.toNat - 400 + 424 ≤ (S.regs 28).toNat + 16 := by
      rw [hk28]; omega
    have a2 : S.regs 2 = BitVec.ofNat 64 (132 - cOf (19 * 0)) := by rw [h2]; simp [cOf]
    have a3 : S.regs 3 = BitVec.ofNat 64 (s.sp.toNat - 400 + 320) := by
      rw [h3, show s.sp.toNat - 400 + 320 = s.sp.toNat - 80 by omega]
    have a4 : S.regs 4 = BitVec.ofNat 64 (cOf (19 * 0) % 4) := by rw [h4]; simp [cOf]
    have a6 : S.regs 6 = BitVec.ofNat 64 (s.sp.toNat - 400 + 352) := by
      rw [h6, show s.sp.toNat - 400 + 352 = s.sp.toNat - 48 by omega]
    have a8 : S.regs 8 = BitVec.ofNat 64 (s.sp.toNat - 400 + 80) := by
      rw [h8, show s.sp.toNat - 400 + 80 = s.sp.toNat - 320 by omega]
    have a11 : Fv256.B.wv S.mem (s.sp.toNat - 400 + 320) 4 = v / 10 ^ (19 * 0) := by
      rw [show s.sp.toNat - 400 + 320 = s.sp.toNat - 80 by omega, hyS, Fv256.B.wv4_eq, hvd]; simp
    have a12 : Fv256.B.wv S.mem (s.sp.toNat - 400 + 352) 4 = 10 ^ 19 := by
      rw [show s.sp.toNat - 400 + 352 = s.sp.toNat - 48 by omega]; exact hdS
    have a13 : S.mem.readLE (s.sp.toNat - 400 + 416) 1 = sep.toNat % 256 := by
      rw [show s.sp.toNat - 400 + 416 = s.sp.toNat + 16 by omega, hsepS, hsepr]
    have a14 : OutIs S.mem (s.sp.toNat - 400 + 231) (sep.toNat % 256) v (cOf (19 * 0)) :=
      OutIs.zero (top := s.sp.toNat - 400 + 231) (M := S.mem) (sep.toNat % 256) v (by
        intro p hp
        rw [show s.sp.toNat - 400 + 231 - p = s.sp.toNat - 169 - p by omega]
        exact hzeroS p hp)
    have a15 : v / 10 ^ (19 * 0) ≠ 0 := by simpa using hz0
    refine Fv256.E.reachesRet64_bind (reachesRet64_link' impl
      (pd_loop (s.sp.toNat - 400) v (sep.toNat % 256) hvlt hsb hb hb16 hb2 4 0 (by omega) S hrS
        a15 hwS htabS hsp h0 a2 a3 a4 a6 a8 hg3S hg1S hg2S hgdS a11 a12 a13 a14).regions) ?_
    intro S2 hrS2 ⟨⟨q10, qsp, q28, q29, q18, qfr, qout, qtab⟩, hregS2⟩
    have hrtv : rtView rt S2.mem = rtView rt s.mem := by
      rw [← hrtv1]
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [(s.sp.toNat - 400 - 368, s.sp.toNat - 400 - 8),
        (s.sp.toNat - 400 + 8, s.sp.toNat - 400 + 392)]) qfr hregS2 ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, by omega, trivial⟩
    have hdl : decLen v ≤ 78 := decLen_le_of_lt_pow v 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
    have hdl1 := decLen_pos v
    have hpl : plen v = decLen v + (decLen v - 1) / 3 := rfl
    have hpl1 : 1 ≤ plen v := by omega
    have hpl2 : plen v ≤ 103 := by omega
    have hX4 : H [0, s.sp.toNat - 400 + 99 + (132 - plen v + 1), 18446744073709551616 - (132 - plen v) - 18446744073709551484]
        (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt S2.mem) := by
      have e1 : s.sp.toNat - 400 + 99 + (132 - plen v + 1) = s.sp.toNat - 168 - plen v := by omega
      have e2 : 18446744073709551616 - (132 - plen v) - 18446744073709551484 = plen v := by omega
      rw [e1, e2, hrtv]; exact hH2
    have hR30 : S.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat := hretS
    janus_run [pdF_val, q10, qsp, hR30, pd_mask (plen v) (by omega) hpl1] calls [hc]
    grab_const Janus.Contracts.StrAt as hright
    grab_frame 4096 as hleft
    obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
    have e2 : 18446744073709551616 - (132 - plen v) - 18446744073709551484 = plen v := by omega
    have e1 : s.sp.toNat - 400 + 99 + (132 - plen v + 1) = s.sp.toNat - 400 + 231 + 1 - plen v := by omega
    have hstr := strBytes_pretty S2.mem (s.sp.toNat - 400 + 231) (sep.toNat % 256) v (by omega) qout (by omega)
    rw [e2, e1] at hr1 hr4
    rw [hstr] at hr1 hr4
    refine ⟨⟨hr1, hr2, hr3, hr4⟩, ?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show s.sp.toNat - 400 - 8 = s.sp.toNat - 408 by omega, hbpS]
      simp
    · exact hk 18 (by simp)
    · have h1 : MemFrame s.mem S.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)]) :=
        hfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h2 : MemFrame S.mem S2.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)]) :=
        qfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h3 := hleft.mono (rs' := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)]) (fun a n h => by
        simp only [outside_append, outside_cons] at h ⊢
        obtain ⟨h1, h2, -⟩ := h
        exact ⟨h1, by omega, by omega, trivial⟩)
      exact h1.trans (h2.trans h3 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
end Fv256.Arm64.Pd
