import Fv256.Arm64.DecProg
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecInit
import Fv256.Arm64.DecIter
import Fv256.Arm64.DecLoop
import Fv256.Arm64.StrconvFormatUint
import Fv256.DecAt
import Fv256.GrabTac

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

/-- A `ReachesRet` of the extracted program is a prefix of a run of the linked program with exit `ret`. -/
theorem reaches_of_reachesRet64 {impl : List Segment} {ret : Nat}
    (hret : RetAddr (Fv256.Arm64.DecProg.program.link impl) ret) {s : State} {t : W64}
    {Q : State → Prop} {R : Outcome → Prop}
    (h : ReachesRet Fv256.Arm64.DecProg.program t s Q)
    (h2 : ∀ s', s'.pc = t → Q s' → Reaches ((Fv256.Arm64.DecProg.program.link impl).withExit ret) s' R) :
    Reaches ((Fv256.Arm64.DecProg.program.link impl).withExit ret) s R := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact Reaches.of_steps (Janus.Program.Steps.withExit (steps_link64 impl hst) hret.fetch_none) (h2 s' hr hq)

set_option maxRecDepth 100000 in
/-- `s` is at the entry of `Dec` (opaque to `omega`). -/
@[irreducible] def AtEntry (s : State) : Prop := s.pc = BitVec.ofNat 64 decE
theorem AtEntry.pc {s : State} (h : AtEntry s) : s.pc = BitVec.ofNat 64 decE := by unfold AtEntry at h; exact h

set_option maxRecDepth 100000 in
theorem decE_seg : decE = segAddr Fv256.Arm64.DecProg.program "github.com/holiman/uint256.(*Int).Dec" := rfl

abbrev zeroDat : Janus.DataSegment := Fv256.Arm64.DecProg.data[0]
set_option maxRecDepth 100000 in
theorem zeroDat_base : zeroDat.base = 960826 := by decide
set_option maxRecDepth 100000 in
theorem zeroDat_len : zeroDat.bytes.length = 256 := by decide
theorem zeroDat_mem : zeroDat ∈ Fv256.Arm64.DecProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
set_option maxRecDepth 100000 in
theorem zeroDat_b0 : zeroDat.bytes[0]! = 48 := by decide +kernel

theorem zeroStr_read {M : Memory} (hd : Fv256.Arm64.DecProg.program.DataLoaded M) :
    M.readLE 960826 1 = 48 ∧ M.accessible 960826 1 false = true := by
  have b0 := dl_byte hd zeroDat_mem 0 (by rw [zeroDat_len]; omega)
  rw [zeroDat_base] at b0
  refine ⟨?_, ?_⟩
  · rw [Nat.add_zero] at b0
    rw [b0]
    have := zeroDat_b0
    simpa [getElem!_pos zeroDat.bytes 0 (by rw [zeroDat_len]; omega)] using this
  · have := dl_acc hd zeroDat_mem
    rw [zeroDat_base, zeroDat_len] at this
    exact accessible_sub this (Or.inl rfl) (by omega) (by omega)

/-- A `ReachesRet` of the extracted program is one of the linked program. -/
theorem reachesRet64_link {P : Janus.Program} (impl : List Segment) {t : W64} {s : State} {Q : State → Prop}
    (h : ReachesRet P t s Q) : ReachesRet (P.link impl) t s Q := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact ⟨k, s', steps_link64 impl hst, hr, hq⟩

/-- A function `Summary` gives the `Ensures` form. -/
theorem ensures_of_summary {p : Janus.Program} {entry : Nat} {args : List W64}
    {spre pre : State → Prop} {Q post : State → State → Prop}
    (hsum : Summary p entry spre Q)
    (hpre : ∀ ret s, RetAddr p ret → CallSetup (p.withExit ret) entry args s → pre s → spre s)
    (hpost : ∀ ret s s', RetAddr p ret → CallSetup (p.withExit ret) entry args s → pre s → Q s s' →
      ABIReturn s s' ∧ post s s') :
    Ensures p entry args pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.pc (hpre ret s hret hs hp)
  refine returns_of_steps (Janus.Program.Steps.withExit hst hret.fetch_none) ?_ (hpost ret s s' hret hs hp hq)
  rw [hr, hs.lr]
  simp only [Janus.Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hret.lt64

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem dec_summary (st : Nat) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Fv256.Arm64.DecProg.program.link impl) ssAddrL rt 4096 H (slicebytetostringSpec st)) :
    Summary (Fv256.Arm64.DecProg.program.link impl) decE
      (fun s => s.regs 0 = z ∧ GuardOK s 688 ∧ StackOK s 4608 8 ∧ Fv256.Arm64.DecProg.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem)) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) ∧
        DecAt rt 989280 1002589 960826 (s'.regs 0).toNat (s'.regs 1).toNat ∧
        (val256 s.mem z.toNat < 100 → MemFrame s.mem s'.mem [(s.sp.toNat - 4608, s.sp.toNat - 8)])) := by
  intro s hpc0 ⟨hz0r, hg, hst, hd, hout, hrt1, hrt2, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hr30, hr30a⟩
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4608, hsp2, hwa⟩ := hst
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hr56 : (s.regs 30).toNat < 72057594037927936 := by omega
  have hdE : decE = 754624 := by unfold decE; decide
  have hrip : AtEntry s := by unfold AtEntry; exact hpc0
  clear hpc0
  simp only [val256] at hH hH1
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
  simp only [val256, hvd]
  have hr4 := s.sp.isLt
  by_cases hbig : 2 ^ 64 ≤ v
  · have hH2 := hH hbig
    have hnb : s.mem.readLE (z.toNat + 8) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 16) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 24) 8 ≠ 0 := by
      refine Decidable.byContradiction fun hcon => ?_
      simp only [not_or, Decidable.not_not] at hcon
      omega
    have e0z : s.regs 0 = z := hz0r
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [e0z]; simp
    have hret30 : (s.regs 30).toNat < 2 ^ 48 := hr30
    have hg_ : GuardOK s 256 := ⟨hg1, hg2, by omega⟩
    refine Fv256.E.reachesRet64_bind (reachesRet64_link impl
      (dec_init s hrip.pc z.toNat e0 hg_ hal (by omega) (by omega) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) hd
        ⟨hzn, hza⟩ (by omega) hret30 hnb).regions) ?_
    intro S hrS ⟨⟨h0, h1, h3, h6, h8, h29, hsp, hk, hfr, hwy, hwd, hzero, htabS, hsv1, hsv2⟩, hregS⟩
    have hwy' : Fv256.B.wv S.mem (s.sp.toNat - 384 + 288) 4 = v := by
      rw [show s.sp.toNat - 384 + 288 = s.sp.toNat - 96 by omega, hwy, Fv256.B.wv4_eq, hvd]
    have hwd' : Fv256.B.wv S.mem (s.sp.toNat - 384 + 320) 4 = 10 ^ 19 := by
      rw [show s.sp.toNat - 384 + 320 = s.sp.toNat - 64 by omega]; exact hwd
    have hwS : S.mem.accessible (s.sp.toNat - 384 - 344) (344 + 384) true = true := by
      rw [hfr.accessible]; exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
    have hg3S : S.mem.readLE ((s.regs 28).toNat + 16) 8 + 304 < s.sp.toNat - 384 := by
      rw [hfr.readLE _ _ (by simp only [Outside, and_true]; omega)]; omega
    have hg2S : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hfr.accessible]; exact hg2
    have e28 : S.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat := by rw [hk 28 (by simp)]; simp
    have hrtv1 : rtView rt S.mem = rtView rt s.mem := by
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [(s.sp.toNat - 392, s.sp.toNat - 32)]) hfr hregS ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, trivial⟩
    refine Fv256.E.reachesRet64_bind (reachesRet64_link impl
      (dec_loop (s.sp.toNat - 384) v (s.regs 28).toNat S.mem hbig hvlt (by omega) (by omega) (by omega) hwS hg3S hg1 hg2S
        (by omega) v 0 S (by simp) (by omega) hrS (by simpa using h0) h1 (by rw [h8]; exact congrArg _ (by omega))
        (by rw [h3]; exact congrArg _ (by omega)) (by rw [h6]; exact congrArg _ (by omega)) (by rw [hsp]) e28
        (MemFrame.refl _ _) hwy' hwd' (fun k hk => by omega) (by simpa using hzero) htabS).regions) ?_
    intro S2 hrS2 ⟨⟨q9, q11, qsp, q28, q29, q18, qfr, qdig, qtab⟩, hregS2⟩
    have hrtv : rtView rt S2.mem = rtView rt s.mem := by
      rw [← hrtv1]
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [(s.sp.toNat - 384 - 344, s.sp.toNat - 384 - 8), (s.sp.toNat - 384 + 8, s.sp.toNat - 384 + 376)]) qfr
        hregS2 ?_
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have := MemFrame.outside_mem hout hr
      simp only [outside_cons]
      exact ⟨by omega, by omega, trivial⟩
    have hdl20 : decLen v ≤ 78 := decLen_le_of_lt_pow v 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
    have hdl1 := decLen_pos v
    have hdlm : decLen v % 18446744073709551616 = decLen v := Nat.mod_eq_of_lt (by omega)
    have hX4 : H [0, s.sp.toNat - 384 + 94 + (98 - decLen v), decLen v] (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt S2.mem) := by
      rw [hrtv]; exact hH2
    have hX3 : 0 < decLen v → s.mem.accessible (s.sp.toNat - 384 + 94 + (98 - decLen v)) (decLen v) false = true :=
      fun _ => accessible_sub hwa (Or.inl rfl) (by omega) (by omega)
    have hX6 : False → Disjoint (s.sp.toNat - 384 + 94 + (98 - decLen v)) (decLen v) 0 32 := fun h => h.elim
    have hR30 : S.mem.readLE (s.sp.toNat - 384) 8 = (s.regs 30).toNat := hsv2
    janus_run [hdE, q9, q11, hdlm, hR30] calls [hc]
    grab_const Janus.Contracts.StrAt as hright
    grab_frame 4096 as hleft
    obtain ⟨⟨hr1, hr2, hr3, hr4⟩, hat⟩ := hright
    have hdig : strBytes S2.mem (s.sp.toNat - 384 + 94 + (98 - decLen v)) (decLen v) = decBytes v :=
      strBytes_dec _ _ _ (fun k hk => by
        have := qdig k hk
        rw [show s.sp.toNat - 384 + 94 + (98 - decLen v) + decLen v - 1 - k = s.sp.toNat - 384 + 94 + 97 - k by omega]
        exact this)
    refine ⟨⟨?_, hr2, hr3, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [hr1, hdig]
    · rw [hr4, hdig]
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show s.sp.toNat - 384 - 8 = s.sp.toNat - 392 by omega, hsv1]
      simp
    · exact hk 18 (by simp)
    · have h1 : MemFrame s.mem S.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) :=
        hfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h2 : MemFrame S.mem S2.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) :=
        qfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h3 : MemFrame S2.mem _ (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) :=
        hleft.mono (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, by omega, trivial⟩)
      refine ⟨h1.trans (h2.trans h3 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩, ?_, fun h => absurd h (by omega)⟩
      simp only [DecAt]; left
      simp only [slicebytetostringSpec, argWords, wordsFrom, arg, List.getD_eq_getElem?_getD, StrAt] at hat
      have h3' : 2 ≤ decLen v := by
        rw [decLen_ge _ (by omega), decLen_ge _ (by omega)]
        have := decLen_pos (v / 10 / 10); omega
      have hlen := hr1
      simp only [strBytes, List.length_map, List.length_range] at hlen
      rcases hat with h | h | h | h <;> first | exact h.2.2 | (exfalso; omega)
  · by_cases hz0 : v = 0
    · have hl0 : s.mem.readLE z.toNat 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hzs := zeroStr_read hd
      have hdj := dl_disjoint hd zeroDat_mem hwa
      rw [zeroDat_base, zeroDat_len] at hdj
      janus_run [hdE, hrip.pc, hl0, hl1', hl2', hl3', Nat.or_eq_zero_iff]
      refine ⟨⟨by rw [hz0]; simp [decBytes_lt 0 (by omega)], hzs.2, ?_⟩, ?_, ?_, fun _ => ?_⟩
      · simp only [hz0, decBytes_lt 0 (by omega), strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
      · refine MemFrame.trans (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)])
          (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
          (MemFrame.of_writeLE _ _ (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
        intro a n h; exact ⟨h, h⟩
      · simp only [DecAt]; right; right; right; constructor <;> simp [setReg] <;> omega
      · refine MemFrame.trans (rs := [(s.sp.toNat - 4608, s.sp.toNat - 8)])
          (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_singleton_self _) (by omega) (by omega))
          (MemFrame.of_writeLE _ _ (rs := [(s.sp.toNat - 4608, s.sp.toNat - 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_singleton_self _) (by omega) (by omega)) ?_
        intro a n h; exact ⟨h, h⟩
    · have hlow : s.mem.readLE (z.toNat + 8) 8 = 0 ∧ s.mem.readLE (z.toNat + 16) 8 = 0 ∧ s.mem.readLE (z.toNat + 24) 8 = 0 := by
        have := hvl.1
        omega
      have hl0 : s.mem.readLE z.toNat 8 = v := by have := hvl.1; omega
      have hv64 : v < 2 ^ 64 := by omega
      have hfu := formatUint_summary st impl rt H hc
      have hdl20 := decLen_le_20 v hv64
      have hdl1 := decLen_pos v
      have hHf : 100 ≤ v → H [0, s.sp.toNat - 384 - 32 + (24 - decLen v), decLen v] (s.regs 28).toNat
          (s.sp.toNat - 384 - 96) (rtView rt s.mem) := fun h => hH1 h hv64
      have hT : TabsOK ((s.mem.writeLE (s.sp.toNat - 392) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 384) 8 (s.regs 30).toNat) := by
        refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.of_loaded hd) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _) ?_ _
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      have hzv : val256 s.mem z.toNat = v := hvd
      janus_run [hdE, hrip.pc, hlow.1, hlow.2.1, hlow.2.2, hl0, Nat.or_eq_zero_iff] calls [hfu]
      clear hfu
      grab_last_const Janus.MemFrame as hqimp
      grab_const Fv256.E.DecAt as hqd
      grab_const Fv256.E.decBytes as hqs
      grab_const Janus.MemFrame as hqf
      refine ⟨hqs, ?_, hqd, fun hlt => ?_⟩
      · have h1 : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 392) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 384) 8 (s.regs 30).toNat)
              (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) := by
            refine MemFrame.trans (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)])
              (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
              (MemFrame.of_writeLE _ _ (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
            intro a n h; exact ⟨h, h⟩
        have h2 := MemFrame.mono (rs' := rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) hqf (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, trivial⟩)
        exact h1.trans h2 fun a n h => ⟨h, h⟩
      · have h1w : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 392) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 384) 8 (s.regs 30).toNat)
            [(s.sp.toNat - 4608, s.sp.toNat - 8)] := by
          refine MemFrame.trans (rs := [(s.sp.toNat - 4608, s.sp.toNat - 8)])
            (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_singleton_self _) (by omega) (by omega))
            (MemFrame.of_writeLE _ _ (rs := [(s.sp.toNat - 4608, s.sp.toNat - 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat - 8)) (List.mem_singleton_self _) (by omega) (by omega)) ?_
          intro a n h; exact ⟨h, h⟩
        have h2w := MemFrame.mono (rs' := [(s.sp.toNat - 4608, s.sp.toNat - 8)]) (hqimp hlt) (fun a n h => by
          simp only [outside_cons, outside_nil, Outside, and_true] at h ⊢
          omega)
        exact h1w.trans h2w fun a n h => ⟨h, h⟩

end Fv256.Arm64.Dec
