import Extracted
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

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

/-- A `ReachesRet` of the extracted program is a prefix of a run of the linked program with exit `ret`. -/
theorem reaches_of_reachesRet64 {impl : List Segment} {ret : Nat}
    (hret : RetAddr (Extracted.program.link impl) ret) {s : State} {t : W64}
    {Q : State → Prop} {R : Outcome → Prop}
    (h : ReachesRet Extracted.program t s Q)
    (h2 : ∀ s', s'.pc = t → Q s' → Reaches ((Extracted.program.link impl).withExit ret) s' R) :
    Reaches ((Extracted.program.link impl).withExit ret) s R := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact Reaches.of_steps (Janus.Program.Steps.withExit (steps_link64 impl hst) hret.fetch_none) (h2 s' hr hq)

abbrev zeroDat : Janus.DataSegment := Extracted.data[1]
set_option maxRecDepth 100000 in
theorem zeroDat_base : zeroDat.base = 960826 := by decide
set_option maxRecDepth 100000 in
theorem zeroDat_len : zeroDat.bytes.length = 256 := by decide
theorem zeroDat_mem : zeroDat ∈ Extracted.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
set_option maxRecDepth 100000 in
theorem zeroDat_b0 : zeroDat.bytes[0]! = 48 := by decide +kernel

theorem zeroStr_read {M : Memory} (hd : Extracted.program.DataLoaded M) :
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

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H slicebytetostringSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hst, hd, hout, hrt1, hrt2, ⟨hza, hzn⟩, hzd, hgd, hH, hH1⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4608, hsp2, hwa⟩ := hst
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
  have hlr : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  by_cases hbig : 2 ^ 64 ≤ v
  · have hH2 := hH hbig
    have hnb : s.mem.readLE (z.toNat + 8) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 16) 8 ≠ 0 ∨ s.mem.readLE (z.toNat + 24) 8 ≠ 0 := by
      refine Decidable.byContradiction fun hcon => ?_
      simp only [not_or, Decidable.not_not] at hcon
      omega
    have e0z : s.regs 0 = z := hs.args 0 (by simp)
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [e0z]; simp
    have hret30 : (s.regs 30).toNat < 2 ^ 48 := by rw [hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]; exact hret.user
    have hg_ : GuardOK s 256 := ⟨hg1, hg2, by omega⟩
    refine returns_of_reaches ?_
    refine reaches_of_reachesRet64 hret
      (dec_init s hs.pc z.toNat e0 hg_ hal (by omega) (by omega) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) hd
        ⟨hzn, hza⟩ (by omega) hret30 hnb).regions ?_
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
    refine reaches_of_reachesRet64 hret
      (dec_loop (s.sp.toNat - 384) v (s.regs 28).toNat S.mem hbig hvlt (by omega) (by omega) (by omega) hwS hg3S hg1 hg2S
        (by omega) v 0 S (by simp) (by omega) hrS (by simpa using h0) h1 (by rw [h8]; exact congrArg _ (by omega))
        (by rw [h3]; exact congrArg _ (by omega)) (by rw [h6]; exact congrArg _ (by omega)) (by rw [hsp]) e28
        (MemFrame.refl _ _) hwy' hwd' (fun k hk => by omega) (by simpa using hzero) htabS).regions ?_
    intro S2 hrS2 ⟨⟨q9, q11, qsp, q28, q29, q18, qfr, qdig, qtab⟩, hregS2⟩
    have hrtv : rtView rt S2.mem = rtView rt s.mem := by
      rw [← hrtv1]
      refine Janus.Contracts.Stack.rtView_eq_of_frame (rs := [(s.sp.toNat - 384 - 344, s.sp.toNat - 384 - 8), (s.sp.toNat - 384 + 8, s.sp.toNat - 384 + 384)]) qfr
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
    have hR30 : S.mem.readLE (s.sp.toNat - 384) 8 = ret := by
      rw [hsv2, hlr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
    janus_run [q9, q11, hdlm, hR30] calls [hc]
    rename_i w8 w7 w6 w5 w4 w3 w2 w1 w0 hleft hright
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hright
    have hdig : strBytes S2.mem (s.sp.toNat - 384 + 94 + (98 - decLen v)) (decLen v) = decBytes v :=
      strBytes_dec _ _ _ (fun k hk => by
        have := qdig k hk
        rw [show s.sp.toNat - 384 + 94 + (98 - decLen v) + decLen v - 1 - k = s.sp.toNat - 384 + 94 + 97 - k by omega]
        exact this)
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, hr2, hr3, ?_⟩, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show s.sp.toNat - 384 - 8 = s.sp.toNat - 392 by omega, hsv1]
      simp
    · exact hk 18 (by simp)
    · rw [hr1, hdig]
    · rw [hr4, hdig]
    · have h1 : MemFrame s.mem S.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) :=
        hfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h2 : MemFrame S.mem S2.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) :=
        qfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h3 : MemFrame S2.mem w2 (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) :=
        hleft.mono (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, by omega, trivial⟩)
      exact h1.trans (h2.trans h3 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · by_cases hz0 : v = 0
    · have hl0 : s.mem.readLE z.toNat 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hzs := zeroStr_read hd
      have hdj := dl_disjoint hd zeroDat_mem hwa
      rw [zeroDat_base, zeroDat_len] at hdj
      janus_run [hl0, hl1', hl2', hl3', Nat.or_eq_zero_iff]
      refine ⟨⟨by rw [hz0]; simp [decBytes_lt 0 (by omega)], hzs.2, ?_⟩, ?_⟩
      · simp only [hz0, decBytes_lt 0 (by omega), strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
      · refine MemFrame.trans (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])
          (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
          (MemFrame.of_writeLE _ _ (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
        intro a n h; exact ⟨h, h⟩
    · have hlow : s.mem.readLE (z.toNat + 8) 8 = 0 ∧ s.mem.readLE (z.toNat + 16) 8 = 0 ∧ s.mem.readLE (z.toNat + 24) 8 = 0 := by
        have := hvl.1
        omega
      have hl0 : s.mem.readLE z.toNat 8 = v := by have := hvl.1; omega
      have hv64 : v < 2 ^ 64 := by omega
      have hfu := formatUint_summary impl rt H hc
      have hdl20 := decLen_le_20 v hv64
      have hdl1 := decLen_pos v
      have hHf : 100 ≤ v → H [0, s.sp.toNat - 384 - 32 + (24 - decLen v), decLen v] (s.regs 28).toNat
          (s.sp.toNat - 384 - 96) (rtView rt s.mem) := fun h => hH1 h hv64
      have hT : TabsOK ((s.mem.writeLE (s.sp.toNat - 392) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 384) 8 ret) := by
        refine TabsOK.writeLE (TabsOK.writeLE (TabsOK.of_loaded hd) (accessible_sub hwa (Or.inr rfl) (by omega) (by omega)) _) ?_ _
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
      have hzv : val256 s.mem z.toNat = v := hvd
      janus_run [hlow.1, hlow.2.1, hlow.2.2, hl0, Nat.or_eq_zero_iff] calls [hfu]
      rename_i hqtab hqs hqf
      refine ⟨hqs, ?_⟩
      have h1 : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 392) 8 (s.regs 29).toNat).writeLE (s.sp.toNat - 384) 8 ret)
            (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) := by
          refine MemFrame.trans (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])
            (MemFrame.of_writeLE s.mem _ (r := (s.sp.toNat - 4608, s.sp.toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
            (MemFrame.of_writeLE _ _ (rs := rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) (r := (s.sp.toNat - 4608, s.sp.toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
          intro a n h; exact ⟨h, h⟩
      have h2 := MemFrame.mono (rs' := rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) hqf (fun a n h => by
        simp only [outside_append, outside_cons] at h ⊢
        obtain ⟨h1, h2, -⟩ := h
        exact ⟨h1, by omega, trivial⟩)
      exact h1.trans h2 fun a n h => ⟨h, h⟩

namespace Witness

open Janus.Contracts.Sat

def implAt : List Segment := [{ name := "model", base := ssAddr, words := constCode 0 0 0 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) ssAddr rtW 4096 H0 slicebytetostringSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, H0, arg, List.getD_eq_getElem?_getD, slicebytetostringSpec] at ha
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  simp [ha, strBytes]

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4608, 4608 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide +kernel

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 688 ∧ StackOK s0 4608 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4608) (4608 + 8) rtW ∧ Outside 989280 256 rtW ∧ Outside 1002589 256 rtW ∧
    Ptr32 s0.mem arg false ∧ (arg.toNat + 32 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 8 ≤ (s0.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s0.mem arg.toNat →
      H0 [0, s0.sp.toNat - 384 + 94 + (98 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 384) (rtView rtW s0.mem)) ∧
    (100 ≤ val256 s0.mem arg.toNat → val256 s0.mem arg.toNat < 2 ^ 64 →
      H0 [0, s0.sp.toNat - 384 - 32 + (24 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 384 - 96) (rtView rtW s0.mem)) := by
  have hz : val256 s0.mem arg.toNat = 0 := by
    unfold val256 s0 arg zp
    decide
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => ?_, fun h _ => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hz] at h; exact absurd h (by decide)
  · rw [hz] at h; exact absurd h (by decide)

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H slicebytetostringSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem))) :=
  ⟨implAt, rtW, H0, ret, s0, arg, model, by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setup, pre⟩

end Witness

end Fv256.Arm64.Dec
