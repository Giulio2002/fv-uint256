import Fv256.PrettyProg
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.PdCells
import Fv256.GrabTac
import Fv256.Amd64.P.T
import Fv256.Util
import Fv256.UtilB2
import Fv256.Amd64.Pd.Tabs
import Fv256.Amd64.Pd.Init
import Fv256.Amd64.Pd.Loop

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E Fv256.Amd64.P

namespace Fv256.Amd64.Pd

abbrev ssAddrL : Nat := Fv256.PrettyProg.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem pdE_val : pdE = 4932000 := by unfold pdE; decide
theorem pdF_val : pdF = 4932726 := by unfold pdF; rw [pdE_val]

theorem pd_mask : ∀ c, c < 134 → 1 ≤ c →
    (132 - c + 1 &&& ((BitVec.ofNat 64 (132 - c) - 132#64).sshiftRight 63).toNat) = 132 - c + 1 := by decide

set_option maxHeartbeats 600000 in
set_option maxRecDepth 200000 in
theorem pd_summary (st : Nat) (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract64 (Fv256.PrettyProg.program.link impl) ssAddrL rt 4096 H (slicebytetostringSpec st)) :
    Summary (Fv256.PrettyProg.program.link impl) pdE
      (fun s => s.regs 0 = z ∧ s.regs 3 = sep ∧ StackGuardOK s 0x378 ∧ StackWritable s 4576 0x18 ∧
        Fv256.PrettyProg.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4576) (4576 + 0x18) rt ∧ (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16) ∧
        (s.mem.readLE z.toNat 32 ≠ 0 →
          H [0, (s.regs 4).toNat - 0xa8 - plen (s.mem.readLE z.toNat 32), plen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x188) (rtView rt s.mem)) ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 140737488355328)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (prettyBytes (sep.toNat % 256) (valueAt s z 32)) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])) := by
  intro s hpc ⟨hz0r, hsepr, hg, hw, hd, hout, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hxx, hdf0, hret47⟩
  have hg_ : StackGuardOK s 0x100 := ⟨hg.noWrap, hg.readable, by have := hg.below; omega⟩
  have hw_ : StackWritable s 0x300 0x18 := ⟨by have := hw.1; omega, by have := hw.2.1; omega,
    by have := hw.2.2; exact accessible_sub this (Or.inr rfl) (by omega) (by omega)⟩
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  have hcE : pdE + 0x5000 < 2 ^ 47 := by decide
  have hr := (s.regs 4).isLt
  have hl0 := Janus.Arm64.Memory.readLE_lt s.mem z.toNat 8
  have hl1 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 8) 8
  have hl2 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 16) 8
  have hl3 := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 24) 8
  simp only [Nat.reducePow] at hl0 hl1 hl2 hl3
  have hv32 := Util.readLE_32 s.mem z.toNat
  obtain ⟨v, hvd⟩ : ∃ v, s.mem.readLE z.toNat 32 = v := ⟨_, rfl⟩
  have hvlt : v < 2 ^ 256 := by rw [← hvd]; simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  rw [hvd] at hH
  by_cases hz0 : v = 0
  · have hv32' := hv32
    have hl0' : s.mem.readLE z.toNat 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [← hvd, hv32] at hz0; omega
    have hzs := zeroStr_read hd
    have hzv : valueAt s z 32 = 0 := by simp only [valueAt]; rw [hvd]; exact hz0
    have hdj := dataLoaded_disjoint hd zeroDat_mem hwa
    rw [zeroDat_base, zeroDat_len] at hdj
    janus64_run [hl0', hl1', hl2', hl3']
    rw [hzv, prettyBytes_lt _ _ (by omega), decBytes_lt 0 (by omega)]
    refine ⟨⟨by simp, hzs.2, ?_⟩, ?_⟩
    · simp only [Spec.strBytes, List.range_one, List.map_cons, List.map_nil]
      rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
    · exact MemFrame.of_writeLE s.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
  · have hH2 := hH hz0
    have hnb : s.mem.readLE z.toNat 32 ≠ 0 := by rw [hvd]; exact hz0
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [hz0r]; simp
    have hb : 0x180 ≤ (s.regs 4).toNat - 384 := by omega
    have hb8 : ((s.regs 4).toNat - 384) % 8 = 0 := by omega
    have hb2 : (s.regs 4).toNat - 384 + 0x198 ≤ 2 ^ 48 := by omega
    have hsb : (s.regs 3).toNat % 256 < 256 := Nat.mod_lt _ (by omega)
    refine Fv256.E.reachesRet_bind' (Fv256.E.reachesRet_link impl
      (pd_init s hpc z.toNat e0 hg_ hw_ hal hd ⟨hzn, hza⟩ (by omega) hnb hxx).regions) ?_
    intro S hrS ⟨⟨h0, h1, h2, h4, h5, h6, h7, h9, h14, hx, hdf, hfr, hsepS, hbpS, hyS, hdS, hzeroS, htabS, hretS⟩, hregS⟩
    have hrtv1 : rtView rt S.mem = rtView rt s.mem := by
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [((s.regs 4).toNat - 0x180, (s.regs 4).toNat + 0x18)]) hfr hregS ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, trivial⟩
    have hwS : S.mem.accessible ((s.regs 4).toNat - 384 - 0x180) (0x180 + 0x198) true = true := by
      rw [hfr.accessible]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    have hg3S : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 0x100 < (s.regs 4).toNat - 384 := by
      rw [h14, hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; omega
    have hg2S : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true := by rw [h14, hfr.accessible]; exact hg2
    have hvlt' : s.mem.readLE z.toNat 32 < 2 ^ 256 := by rw [hvd]; exact hvlt
    have a1 : S.regs 0 = BitVec.ofNat 64 19 := by rw [h0]
    have a2 : S.regs 1 = BitVec.ofNat 64 (132 - cOf (19 * 0)) := by rw [h1]; simp [cOf]
    have a3 : S.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 384 + 0x40) := by rw [h2, show (s.regs 4).toNat - 384 + 0x40 = (s.regs 4).toNat - 320 by omega]
    have a4 : S.regs 6 = BitVec.ofNat 64 (cOf (19 * 0) % 4) := by rw [h6]; simp [cOf]
    have a5 : S.regs 7 = BitVec.ofNat 64 ((s.regs 4).toNat - 384 + 0x130) := by rw [h7, show (s.regs 4).toNat - 384 + 0x130 = (s.regs 4).toNat - 80 by omega]
    have a6 : S.regs 9 = BitVec.ofNat 64 ((s.regs 4).toNat - 384 + 0x150) := by rw [h9, show (s.regs 4).toNat - 384 + 0x150 = (s.regs 4).toNat - 48 by omega]
    have a7 : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 384) := by rw [h4]
    have a8 : S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 384 + 0x178) := by rw [h5, show (s.regs 4).toNat - 384 + 0x178 = (s.regs 4).toNat - 8 by omega]
    have a9 : (S.regs 14).toNat + 24 ≤ 2 ^ 48 := by rw [h14]; omega
    have a10 : ((S.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 384 - 0x180 ∨ (s.regs 4).toNat - 384 + 0x198 ≤ (S.regs 14).toNat + 16) := by
      rw [h14]; omega
    have a11 : Fv256.B.wv S.mem ((s.regs 4).toNat - 384 + 0x130) 4 = s.mem.readLE z.toNat 32 / 10 ^ (19 * 0) := by
      rw [Fv256.B.wv4_eq, show (s.regs 4).toNat - 384 + 0x130 = (s.regs 4).toNat - 80 by omega, hyS]; simp
    have a12 : Fv256.B.wv S.mem ((s.regs 4).toNat - 384 + 0x150) 4 = 10 ^ 19 := by
      rw [Fv256.B.wv4_eq, show (s.regs 4).toNat - 384 + 0x150 = (s.regs 4).toNat - 48 by omega]; exact hdS
    have a13 : S.mem.readLE ((s.regs 4).toNat - 384 + 0x190) 1 = (s.regs 3).toNat % 256 := by
      rw [show (s.regs 4).toNat - 384 + 0x190 = (s.regs 4).toNat + 16 by omega]; exact hsepS
    have a14 : OutIs S.mem ((s.regs 4).toNat - 384 + 215) ((s.regs 3).toNat % 256) (s.mem.readLE z.toNat 32) (cOf (19 * 0)) := by
      have := OutIs.zero (top := (s.regs 4).toNat - 384 + 215) (M := S.mem) ((s.regs 3).toNat % 256) (s.mem.readLE z.toNat 32) (by
        intro p hp
        rw [show (s.regs 4).toNat - 384 + 215 - p = (s.regs 4).toNat - 169 - p by omega]
        exact hzeroS p hp)
      exact this
    have a15 : s.mem.readLE z.toNat 32 / 10 ^ (19 * 0) ≠ 0 := by simpa using hnb
    refine Fv256.E.reachesRet_bind' (Fv256.E.reachesRet_link impl
      (pd_loop ((s.regs 4).toNat - 384) (s.mem.readLE z.toNat 32) ((s.regs 3).toNat % 256) hvlt' hsb hb hb8 hb2 4 0 (by omega) S hrS
        a15 hwS htabS hx (hdf.trans hdf0) a1 a2 a3 a4 a5 a6 a7 a8 hg3S a9 hg2S a10 a11 a12 a13 a14).regions) ?_
    intro S2 hrS2 ⟨⟨q12, q4, q5, q14, qx, qdf, qfr, qout, qtab⟩, hregS2⟩
    have hrip2 : S2.rip = BitVec.ofNat 64 pdF := hrS2
    have hdl : decLen v ≤ 78 := decLen_le_of_lt_pow v 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
    have hdl1 := decLen_pos v
    have hpl : plen v = decLen v + (decLen v - 1) / 3 := rfl
    have hpl1 : 1 ≤ plen v := by omega
    have hpl2 : plen v ≤ 103 := by omega
    rw [hvd] at q12 qout
    have hfrAll : MemFrame s.mem S2.mem [((s.regs 4).toNat - 0x300, (s.regs 4).toNat + 0x18)] :=
      MemFrame.trans (rs := [((s.regs 4).toNat - 0x300, (s.regs 4).toNat + 0x18)]) (rs' := [((s.regs 4).toNat - 0x300, (s.regs 4).toNat + 0x18)])
        (hfr.mono (by intro a n h; simp only [Outside, and_true] at h ⊢; omega))
        (qfr.mono (by intro a n h; simp only [Outside, and_true] at h ⊢; omega)) (fun a n h => ⟨h, h⟩)
    have hrtv : rtView rt S2.mem = rtView rt s.mem := by
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [((s.regs 4).toNat - 0x300, (s.regs 4).toNat + 0x18)]) hfrAll (hregS2.trans hregS) ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, trivial⟩
    have hX4 : H [0, (s.regs 4).toNat - 384 + (132 - plen v + 1) + 83, 18446744073709551616 - (18446744073709551484 + (132 - plen v))]
        (s.regs 14).toNat ((s.regs 4).toNat - 384 - 8) (rtView rt S2.mem) := by
      have e1 : (s.regs 4).toNat - 384 + (132 - plen v + 1) + 83 = (s.regs 4).toNat - 0xa8 - plen v := by omega
      have e2 : 18446744073709551616 - (18446744073709551484 + (132 - plen v)) = plen v := by omega
      rw [e1, e2, show (s.regs 4).toNat - 384 - 8 = (s.regs 4).toNat - 0x188 by omega, hrtv]
      exact hH2
    have hX7 : S.mem.readLE ((s.regs 4).toNat - 384 + 384) 8 < 140737488355328 := by
      rw [show (s.regs 4).toNat - 384 + 384 = (s.regs 4).toNat by omega, hretS]; exact hret47
    have hretS2 : S.mem.readLE ((s.regs 4).toNat - 384 + 384) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [show (s.regs 4).toNat - 384 + 384 = (s.regs 4).toNat by omega]; exact hretS
    janus64_run [hrip2, pdF_val, q12, q4, q5, q14, hretS2, pd_mask (plen v) (by omega) hpl1] calls [hc]
    grab_const Janus.Contracts.StrAt as hright
    grab_frame 4096 as hleft
    obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
    have e2 : 18446744073709551616 - (18446744073709551484 + (132 - plen v)) = plen v := by omega
    have e1 : (s.regs 4).toNat - 384 + (132 - plen v + 1) + 83 = (s.regs 4).toNat - 384 + 215 + 1 - plen v := by omega
    have hstr := strBytes_pretty S2.mem ((s.regs 4).toNat - 384 + 215) ((s.regs 3).toNat % 256) v (by omega) qout (by omega)
    rw [e2, e1] at hr1 hr4
    rw [hstr] at hr1 hr4
    have hzv : valueAt s z 32 = v := by simp only [valueAt]; exact hvd
    have hsepv : sep.toNat % 256 = (s.regs 3).toNat % 256 := by rw [hsepr]
    rw [hzv, hsepv]
    refine ⟨⟨hr1, hr2, hr3, hr4⟩, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show (s.regs 4).toNat - 384 + 376 = (s.regs 4).toNat - 8 by omega, hbpS]
      simp
    · have h3 : MemFrame S2.mem (Arm64.Memory.writeLE S2.mem ((s.regs 4).toNat - 384 - 8) 8 4932781)
          (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)]) :=
        MemFrame.of_writeLE S2.mem 4932781 (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
      have h4 := hleft.mono (rs' := rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)]) (fun a n h => by
        simp only [outside_append, outside_cons] at h ⊢
        obtain ⟨h1, h2, -⟩ := h
        exact ⟨h1, by omega, by omega, trivial⟩)
      refine MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])
        (rs' := rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)]) ?_ (MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])
        (rs' := rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)]) h3 h4 (fun a n h => ⟨h, h⟩)) (fun a n h => ⟨h, h⟩)
      exact hfrAll.mono (fun a n h => by
        simp only [outside_append, outside_cons, Outside, and_true] at h ⊢
        omega)
end Fv256.Amd64.Pd
