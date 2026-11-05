import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecT
import Fv256.Amd64.DecInit
import Fv256.Amd64.DecIter
import Fv256.Amd64.DecLoop
import Fv256.Amd64.StrconvFormatUint

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev zeroDat : Janus.DataSegment := Extracted.data[1]
set_option maxRecDepth 100000 in
theorem zeroDat_base : zeroDat.base = 5134938 := by decide
set_option maxRecDepth 100000 in
theorem zeroDat_len : zeroDat.bytes.length = 256 := by decide
theorem zeroDat_mem : zeroDat ∈ Extracted.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
set_option maxRecDepth 100000 in
theorem zeroDat_b0 : zeroDat.bytes[0]! = 48 := by decide +kernel

theorem zeroStr_read {M : Memory} (hd : Extracted.program.DataLoaded M) :
    M.readLE 5134938 1 = 48 ∧ M.accessible 5134938 1 false = true := by
  have b0 := DataLoaded.byte hd zeroDat_mem 0 (by rw [zeroDat_len]; omega)
  rw [zeroDat_base] at b0
  refine ⟨?_, ?_⟩
  · rw [Nat.add_zero] at b0
    rw [b0]
    have := zeroDat_b0
    simpa [getElem!_pos zeroDat.bytes 0 (by rw [zeroDat_len]; omega)] using this
  · have := DataLoaded.accessible hd zeroDat_mem
    rw [zeroDat_base, zeroDat_len] at this
    exact accessible_sub this (Or.inl rfl) (by omega) (by omega)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H slicebytetostringSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 0x378 ∧ StackWritable s 4568 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4568) (4568 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 384 - 0x58) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hout, hrt1, hrt2, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1⟩
  janus64_intro hs
  janus64_intro hs
  have hg_ : StackGuardOK s 0xf8 := ⟨hg.noWrap, hg.readable, by have := hg.below; omega⟩
  have hw_ : StackWritable s 0x318 0x8 := ⟨by have := hw.1; omega, by have := hw.2.1; omega,
    by have := hw.2.2; exact accessible_sub this (Or.inr rfl) (by omega) (by omega)⟩
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
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
    have hx15 : s.xmm 15 = 0 := hs.zero
    have e0z : s.regs 0 = z := hs.args 0 (by simp)
    have e0 : s.regs 0 = BitVec.ofNat 64 z.toNat := by rw [e0z]; simp
    have hrip := hs.rip
    refine returns_of_reaches ?_
    refine reaches_of_reachesRet hret
      (dec_init s hrip z.toNat e0 hg_ hw_ hal hd ⟨hzn, hza⟩ (by omega) hnb hx15).regions ?_
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
    refine reaches_of_reachesRet hret
      (dec_loop ((s.regs 4).toNat - 0x178) v (s.regs 14).toNat S.mem hbig hvlt hbb
        (by omega) (by omega) hwb2 hg3S (by omega) hg2S (by omega) v 0 S
        (by simp) (by omega) hrS (by simpa using h0) h1 (by simpa using h2) h4 h5 h7 h9
        (by rw [h14]; simp) hx (hdf.trans hs.df) (MemFrame.refl _ _) hwy' hwd (fun k hk => by omega) (by simpa using hzero) htabS).regions ?_
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
    have hX8 : s.mem.readLE ((s.regs 4).toNat - 376 + 376) 8 = ret := by
      rw [show (s.regs 4).toNat - 376 + 376 = (s.regs 4).toNat by omega]
      exact hs.ret
    have hX5 : (s.regs 4).toNat - 376 + 86 + (98 - decLen v) + decLen v ≤ 281474976710656 := by omega
    janus64_run [q2, q13, q4, q5, q14, hdlm, hX8] calls [hc]
    rename_i w9 w8 w7 w6 w5 w4 w3 w2 w1 w0 hleft hright
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hright
    have hdig : Spec.strBytes S2.mem ((s.regs 4).toNat - 376 + 86 + (98 - decLen v)) (decLen v) = decBytes v :=
      strBytes_dec _ _ _ (fun k hk => by
        have := qdig k hk
        rw [show (s.regs 4).toNat - 376 + 86 + (98 - decLen v) + decLen v - 1 - k = (s.regs 4).toNat - 376 + 86 + 97 - k by omega]
        exact this)
    refine ⟨⟨?_, ?_⟩, ⟨?_, hr2, hr3, ?_⟩, ?_⟩
    · have hx := (s.regs 4).isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · rw [show (s.regs 4).toNat - 376 + 368 = (s.regs 4).toNat - 8 by omega, hbp]
      simp
    · rw [hr1, hdig]; simp [valueAt, hvd]
    · rw [hr4, hdig, valueAt, hvd]
    · have h1 : MemFrame s.mem S.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        hfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h2 : MemFrame S.mem S2.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        qfr.mono (fun a n h => by simp only [outside_append, outside_cons, Outside, and_true] at h ⊢; omega)
      have h3 : MemFrame S2.mem (Arm64.Memory.writeLE S2.mem ((s.regs 4).toNat - 376 - 8) 8 4931926)
          (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        MemFrame.of_writeLE S2.mem 4931926 (List.mem_append_right _ (List.mem_singleton_self _)) (by simp; omega) (by simp; omega)
      have h4 : MemFrame (Arm64.Memory.writeLE S2.mem ((s.regs 4).toNat - 376 - 8) 8 4931926) w2
          (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) :=
        hleft.mono (fun a n h => by
          simp only [outside_append, outside_cons] at h ⊢
          obtain ⟨h1, h2, -⟩ := h
          exact ⟨h1, by omega, by omega, trivial⟩)
      exact h1.trans (h2.trans (h3.trans h4 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · by_cases hz0 : v = 0
    · have hl0 : s.mem.readLE z.toNat 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl1' : s.mem.readLE (z.toNat + 8) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl2' : s.mem.readLE (z.toNat + 16) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hl3' : s.mem.readLE (z.toNat + 24) 8 = 0 := by rw [hvl.1] at hz0; omega
      have hzs := zeroStr_read hd
      have hzv : valueAt s z 32 = 0 := by simp only [valueAt]; rw [hvd]; exact hz0
      have hdj := dataLoaded_disjoint hd zeroDat_mem hwa
      rw [zeroDat_base, zeroDat_len] at hdj
      janus64_run [hl0, hl1', hl2', hl3']
      rw [hzv]
      refine ⟨⟨by simp [decBytes_lt 0 (by omega)], hzs.2, ?_⟩, ?_⟩
      · simp only [decBytes_lt 0 (by omega), Spec.strBytes, List.range_one, List.map_cons, List.map_nil]
        rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hzs.1]
      · exact MemFrame.of_writeLE s.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
    · have hlow : s.mem.readLE (z.toNat + 8) 8 = 0 ∧ s.mem.readLE (z.toNat + 16) 8 = 0 ∧ s.mem.readLE (z.toNat + 24) 8 = 0 := by
        have := hvl.1
        omega
      have hl0 : s.mem.readLE z.toNat 8 = v := by have := hvl.1; omega
      have hv64 : v < 2 ^ 64 := by omega
      have hfu := formatUint_summary impl rt H hc
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
      janus64_run [hlow.1, hlow.2.1, hlow.2.2, hl0, hnzv] calls [hfu]
      rename_i hqtab hqs hqf
      rw [hzv]
      obtain ⟨q1, q2, q3, q4⟩ := hqs
      refine ⟨⟨q1, q2, q3, q4⟩, ?_⟩
      have h1 : MemFrame s.mem (((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
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

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (rtW H0)

def implAt : List Amd64.Segment := [{ name := "model", base := ssAddr, bytes := constCode64 0 0 0 }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) ssAddr rtW 4096 H0 slicebytetostringSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  simp only [slicebytetostringSpec] at ha ⊢
  simp [ha, Spec.strBytes]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4568, 4568 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0x378 ∧ StackWritable s0 4568 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4568) (4568 + 8) rtW ∧ Outside 5163273 256 rtW ∧ Outside 5176582 256 rtW ∧
    (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4568 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4568 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s0.mem.readLE arg.toNat 32 →
      H0 [0, (s0.regs 4).toNat - 0x178 + 86 + (98 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 0x178 - 8) (rtView rtW s0.mem)) ∧
    (100 ≤ s0.mem.readLE arg.toNat 32 → s0.mem.readLE arg.toNat 32 < 2 ^ 64 →
      H0 [0, (s0.regs 4).toNat - 384 - 0x20 + (24 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 384 - 0x58) (rtView rtW s0.mem)) := by
  have hz : s0.mem.readLE arg.toNat 32 = 0 := by
    unfold s0 arg zp
    decide
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => ?_, fun h _ => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hz] at h; exact absurd h (by decide)
  · rw [hz] at h; exact absurd h (by decide)

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H slicebytetostringSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 0x378 ∧ StackWritable s 4568 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4568) (4568 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      H [0, (s.regs 4).toNat - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 0x178 - 8) (rtView rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (s.regs 4).toNat - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 384 - 0x58) (rtView rt s.mem))) :=
  ⟨implAt, rtW, H0, ret, s0, arg, model, by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setup, pre⟩

end Witness

end Fv256.Amd64.Dec
