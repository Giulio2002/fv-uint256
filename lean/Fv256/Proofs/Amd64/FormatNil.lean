import Extracted
import Fv256.Proofs.Common.GrabRet
import Fv256.Proofs.Common.SpecFormat
import Fv256.Spec.Amd64.FormatNil

/-!
# `(*uint256.Int).Format`, path (i): the nil receiver (amd64)

From the split state `S0` at `Format+0x20` with `z == 0` (RAX = 0): `w := s.(io.Writer)` (`runtime.typeAssert`, with the inline cache probe;
a nil `s.itab` gives a nil writer), then `fmt.Fprint(w, "<nil>")` (a static `ICallContract64` at `contractAddr "fmt.Fprint"`), epilogue, return.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
  Janus.Spec Janus.Spec.Type

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.janusRenameI false
set_option linter.unusedVariables false

namespace Fv256.Amd64.FormatNil

/-- the precondition at `S0 = Format+0x20`, `z = 0` -/
def NilPre (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State) : Prop :=
  S0.regs 0 = 0#64 ∧ S0.regs 3 = tab ∧ S0.regs 1 = data ∧ S0.regs 5 = S0.regs 4 + 64#64 ∧
  (S0.regs 4).toNat % 8 = 0 ∧ 8 + stack ≤ (S0.regs 4).toNat ∧ (S0.regs 4).toNat + 0x78 ≤ 2 ^ 48 ∧
  S0.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true ∧
  Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt ∧
  S0.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat ∧ S0.mem.readLE ((S0.regs 4).toNat + 0x48) 8 < 2 ^ 47 ∧
  S0.xmm 15 = 0 ∧ S0.df = false ∧
  -- the interface runtime (typeAssert): the caller's window `[r-8-depth, r+0x78)` (the call pushes 8 bytes)
  CallerOK R S0 8 0x78 ∧
  TADescOK R S0.mem descA ∧ Outside descA 24 [((S0.regs 4).toNat - 8 - R.depth, (S0.regs 4).toNat + 0x78)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ S0.mem.accessible tab.toNat 0x14 false = true ∧ tyOf S0 tab ≠ 0 ∧ R.IsType (tyOf S0 tab) ∧
    (taCanFail S0.mem descA = true ∨ (R.itab (taInter S0.mem descA) (tyOf S0 tab)).isSome)) ∧
  -- the literal "<nil>" and its header: read-only data, away from every written range
  S0.mem.readLE hdrA 8 = litA ∧ S0.mem.readLE (hdrA + 8) 8 = 5 ∧
  StrOut S0.mem litA 5 Fv256.FormatSpec.nilText ∧
  Outside hdrA 16 (NilFL R rt (S0.regs 4).toNat stack) ∧ Outside litA 5 (NilFL R rt (S0.regs 4).toNat stack)

/-- the state at `Format+0x208` (the `Fprint` setup), after the `typeAssert` part -/
def Mid (R : IfaceModel) (tab data : BitVec 64) (S0 S1 : State) : Prop :=
  (S1.regs 3).toNat = wOf R S0 tab ∧ S1.regs 1 = data ∧ S1.regs 4 = S0.regs 4 ∧ S1.regs 5 = S0.regs 5 ∧
  S1.regs 14 = S0.regs 14 ∧ S1.xmm 15 = S0.xmm 15 ∧ S1.df = S0.df ∧ S1.fsBase = S0.fsBase ∧
  MemFrame S0.mem S1.mem (TAFL R (S0.regs 4).toNat)

/-- the postcondition at the return -/
def NilQ (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64) (S0 S' : State) : Prop :=
  S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
  S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧ S'.df = S0.df ∧ S'.fsBase = S0.fsBase ∧
  MemFrame S0.mem S'.mem (NilFL R rt (S0.regs 4).toNat stack) ∧
  ∃ j0 j3 j1, RFp (BitVec.ofNat 64 (wOf R S0 tab)) data (BitVec.ofNat 64 ((S0.regs 4).toNat + 0x30)) 1#64 j0 j3 j1

/-- the frame of the whole path after the `Fprint` call: `typeAssert`'s frame, the three stores of the call setup, the callee's frame -/
theorem frame_fp {R : IfaceModel} {rt : List (Nat × Nat)} {stack r : Nat} {m0 m1 m : Memory} {a b c : Nat}
    (mfr : MemFrame m0 m1 (TAFL R r)) (hwb : 8 + stack ≤ r)
    (hfr : MemFrame (((m1.writeLE (r + 48) 8 a).writeLE (r + 56) 8 b).writeLE (r - 8) 8 c) m
      (rt ++ [(r - 8 - stack, r - 8), (r - 8 + 8, r - 8 + 8 + 40)])) :
    MemFrame m0 m (NilFL R rt r stack) := by
  have h1 : MemFrame m0 m1 (NilFL R rt r stack) := mfr.mono fun a n h => by
    simp only [NilFL, outside_append] at h; exact h.1.2
  have h2 : MemFrame m1 (((m1.writeLE (r + 48) 8 a).writeLE (r + 56) 8 b).writeLE (r - 8) 8 c) (NilFL R rt r stack) :=
    ((((MemFrame.refl m1 _).writeLE a (r := (r + 0x30, r + 0x40)) (by simp [NilFL]) (by simp) (by simp)).writeLE b
      (r := (r + 0x30, r + 0x40)) (by simp [NilFL]) (by simp) (by simp)).writeLE c (r := (r - 8 - stack, r + 40))
      (by simp [NilFL]) (by simp) (by simp; omega))
  have h3 : MemFrame (((m1.writeLE (r + 48) 8 a).writeLE (r + 56) 8 b).writeLE (r - 8) 8 c) m (NilFL R rt r stack) :=
    hfr.mono fun a n h => by
      simp only [NilFL, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨h1, -⟩, h3, h4⟩ := h
      refine ⟨h1, ?_, ?_⟩ <;> omega
  exact (h1.trans h2 fun a n h => ⟨h, h⟩).trans h3 fun a n h => ⟨h, h⟩

theorem tail (impl : List Amd64.Segment) (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64)
    (hFp : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (FpArg data))
    (S0 S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (Extracted.entry + 0x208))
    (hpre : NilPre R rt stack tab data S0) (hm : Mid R tab data S0 S1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S1
      (NilQ R rt stack RFp tab data S0) := by
  obtain ⟨h0', h3', h1', h5', hal, hwb, hwn, hwa, hout, hs60, hr47, hx0, hdf0, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre
  obtain ⟨m3, m1, m4, m5, m14, mx, mdf, mfs, mfr⟩ := hm
  have hdrL : hdrA = 5181840 := rfl
  have litL : litA = 5135382 := by decide
  simp only [hdrL, litL] at hhdr hhn hlit hho hlo
  simp only [NilFL, outside_append] at hho hlo
  obtain ⟨⟨hho1, hho2⟩, hho3⟩ := hho
  obtain ⟨⟨hlo1, hlo2⟩, hlo3⟩ := hlo
  simp only [outside_cons, outside_nil, and_true] at hho3 hlo3
  have e1 : S1.mem.readLE 5181840 8 = 5135382 := by
    rw [mfr.readLE _ _ (hho2.of_sub (by omega) (by omega))]; exact hhdr
  have e2 : S1.mem.readLE (5181840 + 8) 8 = 5 := by
    rw [mfr.readLE _ _ (hho2.of_sub (by omega) (by omega))]; exact hhn
  have e3 : S1.mem.accessible 5135382 5 false = true := by
    rw [mfr.accessible]; exact hlit.2.2.1 (by decide)
  have e4 : strBytes S1.mem 5135382 5 = Fv256.FormatSpec.nilText := by
    rw [strBytes_of_frame mfr hlo2]; exact hlit.2.2.2
  have e4' : strBytes S1.mem litA 5 = Fv256.FormatSpec.nilText := by rw [litL]; exact e4
  have hT : Outside ((S0.regs 4).toNat + 64) 16 (TAFL R (S0.regs 4).toNat) := by
    simp only [TAFL, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨hcall.2.2.2.2.2.2.1.of_sub (by omega) (by omega), by omega, ?_⟩
    simp only [outside_cons, outside_nil, and_true] at hdo
    omega
  have hr72 : S1.mem.readLE ((S0.regs 4).toNat + 72) 8 = S0.mem.readLE ((S0.regs 4).toNat + 72) 8 :=
    mfr.readLE _ _ (hT.of_sub (by omega) (by omega))
  have hr64 : S1.mem.readLE ((S0.regs 4).toNat + 64) 8 = S0.mem.readLE ((S0.regs 4).toNat + 64) 8 :=
    mfr.readLE _ _ (hT.of_sub (by omega) (by omega))
  janus64_run [hr72, hr64, hr47, e1, e2, e3, e4, e4', Janus.Spec.strBytes_writeLE] calls [hFp]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have hS1 : S1.regs 3 = BitVec.ofNat 64 (wOf R S0 tab) := by rw [← m3]; simp
  have hA : S0.regs 4 + 48#64 = BitVec.ofNat 64 ((S0.regs 4).toNat + 48) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp
  unfold NilQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [setRegF_apply])
  · simp
  · simp
  · simp [callRegs64_apply, setRegF_apply, m14]
  · simp [hx0]
  · simp [hdf0]
  · exact mfs
  · exact frame_fp mfr hwb hfr
  · refine ⟨junk 0, junk 3, junk 1, ?_⟩
    rw [← hS1, ← hA]; exact hR

/-- the frame of the `typeAssert` call: the pushed return address, then the runtime's own writes -/
theorem frame_ta {R : IfaceModel} {r v : Nat} {m0 m : Memory} (hr : 8 ≤ r)
    (hfr : MemFrame (m0.writeLE (r - 8) 8 v) m
      (R.priv ++ [(r - 8 - R.depth, r - 8), (r - 8 + 8, r - 8 + 8 + 8 * 2)] ++ [(descA, descA + 8)])) :
    MemFrame m0 m (TAFL R r) := by
  have h1 : MemFrame m0 (m0.writeLE (r - 8) 8 v) (TAFL R r) :=
    MemFrame.of_writeLE m0 v (r := (r - 8 - R.depth, r + 16)) (by simp [TAFL]) (by simp) (by simp; omega)
  have h2 : MemFrame (m0.writeLE (r - 8) 8 v) m (TAFL R r) :=
    hfr.mono fun a n h => by
      simp only [TAFL, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨⟨h1, by omega, by omega⟩, h3⟩
  exact h1.trans h2 fun a n h => ⟨h, h⟩

/-- the registers and memory at the `typeAssert` probe, shared by the miss, hit and loop lemmas -/
def PState (R : IfaceModel) (tab data : BitVec 64) (S0 S : State) : Prop :=
  S.regs 2 = BitVec.ofNat 64 (tyOf S0 tab) ∧ S.regs 1 = data ∧ S.regs 4 = S0.regs 4 ∧ S.regs 5 = S0.regs 5 ∧
  S.regs 14 = S0.regs 14 ∧ S.xmm 15 = S0.xmm 15 ∧ S.df = S0.df ∧ S.fsBase = S0.fsBase ∧ S.mem = S0.mem

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- a cache miss: the call of `runtime.typeAssert` (`Format+0x25b`) and the jump to `Format+0x208` -/
theorem miss (impl : List Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 S : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem))
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x25b)) (hps : PState R tab data S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S (Mid R tab data S0) := by
  obtain ⟨h0', h3', h1', h5', hal, hwb, hwn, hwa, hout, hs60, hr47, hx0, hdf0, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre
  obtain ⟨p2, p1, p4, p5, p14, px, pdf, pfs, pm⟩ := hps
  obtain ⟨ht0, hty, hcf⟩ := htab htz |>.2.2
  have hc' := hcall
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal2, hd2, hb2, hst2, hout2, hgd, hgo⟩ := hc'
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal2 hd2 hb2 hst2 hout2
  have hdo' : Outside descA 24 [((S0.regs 4).toNat - (R.depth + 8), (S0.regs 4).toNat + 0x78)] := by
    simp only [outside_cons, outside_nil, and_true] at hdo ⊢; omega
  have hsp8 : (S0.regs 4 - 8#64).toNat = (S0.regs 4).toNat - 8 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hsp8' : (18446744073709551608 + (S0.regs 4).toNat) % 18446744073709551616 = (S0.regs 4).toNat - 8 := by omega
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((S0.regs 4).toNat - (R.depth + 8), (S0.regs 4).toNat + 0x78)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout2 (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo'' : Outside descA 24 [((S0.regs 4).toNat - (R.depth + 8), (S0.regs 4).toNat + 0x78)] := hdo'
  have hD : descA = 5996832 := rfl
  have hd64 : (5996832 : Nat) % 2 ^ 64 = 5996832 := by decide
  have hdA64 : descA % 2 ^ 64 = descA := by rw [hD]
  have htl : tyOf S0 tab % 2 ^ 64 = tyOf S0 tab := Nat.mod_eq_of_lt (by
    have := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 8) 8; simpa [tyOf] using this)
  janus64_run until [Extracted.program.contractAddr "runtime.typeAssert"]
  refine ReachesRet.call hta rfl
    ⟨RTPre.of_caller hl hcall (by janus_frame) (by simp [setRegF, hsp8]) (by simp [setRegF, p14]) (by simp [px, hx0])
      (by simp [pdf, hdf0]) (by simp [setRegF, hsp8, hsp8', Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide), ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, ← hD]
    exact TADescOK.frame hdesc (by janus_frame) hdo'' hws
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, htl]; exact ht0
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, htl, ← hD, hdA64]
    intro _; refine ⟨hty, ?_⟩
    rw [taCanFail_frame (m := S0.mem) (by janus_frame) hdo'', taInter_frame (m := S0.mem) (by janus_frame) hdo'']
    exact hcf
  · simp only [Janus.Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, htl, ← hD, hdA64, p14]
    simp (disch := janus64_disch) only [Janus.Contracts.rtView_writeLE]
    simpa [hsp8] using hH
  · intro s' hpc' ⟨rr, x', y, fl, m', zh', kr', hs', hfr, henv', hres, hdesc2, hinter2, hcf2⟩
    subst hs'
    simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, hdA64, htl, hsp8, hsp8', ← hD] at hfr hres hdesc2 hinter2 hcf2
    janus64_run until [Extracted.entry + 0x208]
    have hMf : MemFrame S0.mem (Arm64.Memory.writeLE S0.mem ((S0.regs 4).toNat - 8) 8 4923946)
        [((S0.regs 4).toNat - (R.depth + 8), (S0.regs 4).toNat + 0x78)] := by janus_frame
    rw [taInter_frame hMf hdo''] at hres
    have hr60 : m'.readLE ((S0.regs 4).toNat + 96) 8 = data.toNat := by
      rw [hfr.readLE _ _ ?_]
      · rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hs60
      · simp only [outside_append, outside_cons, outside_nil, and_true]
        simp only [outside_cons, outside_nil, and_true] at hdo''
        refine ⟨⟨hout2.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
    refine ReachesRet.done (by simp [Extracted.entry]) ?_
    unfold Mid
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp only [setRegF_apply, MapAmd64.keepABI_apply, MapAmd64.keepX15_apply])
    · simp only [ite_true]
      rw [hres.1]; simp [wOf, htz, ht0]
    · simp only [ite_true, hr60]; simp
    · simp [BitVec.sub_add_cancel]
    · simp [p5]
    · simp [p14]
    · simp [px]
    · simp [hdf0]
    · simp [pfs]
    · exact frame_ta (by omega) hfr

/-- the entry address the probe computes (`((h & Mask) << 4) + cache + 8`) -/
theorem probeAddr (h : BitVec 64) (k : Nat) (hk : k ≤ 64) (hc : 16 * 2 ^ k ≤ 2 ^ 48) :
    ((h &&& BitVec.ofNat 64 (2 ^ k - 1)) <<< 4).toNat = 16 * (h.toNat % 2 ^ k) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  rw [Janus.Tactic.bv_toNat_shiftLeft, Janus.Contracts.Iface.and_mask_toNat h k hk, Nat.mod_eq_of_lt (by omega)]

/-- a cache hit at entry `i` (`Format+0x274`): the cached itab is the runtime's answer -/
theorem hit (impl : List Amd64.Segment) (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64)
    (S0 S : State) (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (k : Nat) (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (i : Nat) (hi : i < 2 ^ k) (hty : taTyp S0.mem (S0.mem.readLE descA 8) i = tyOf S0 tab)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x274)) (hps : PState R tab data S0 S)
    (h8 : S.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8)) (h10 : (S.regs 10).toNat = 16 * i) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S (Mid R tab data S0) := by
  obtain ⟨p2, p1, p4, p5, p14, px, pdf, pfs, pm⟩ := hps
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx0, hdf0, hcall, hdesc, hdo, htab, -⟩ := hpre
  obtain ⟨ht0, hty0, -⟩ := htab htz |>.2.2
  have hit' : Arm64.Memory.readLE S0.mem (16 * i + (S0.mem.readLE descA 8 + 16)) 8 =
      (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0 := by
    have := hent i hi (by rw [hty]; exact ht0)
    rw [hty] at this
    rw [← this]; simp only [taItab]
    rw [show S0.mem.readLE descA 8 + 16 + 16 * i = 16 * i + (S0.mem.readLE descA 8 + 16) by omega]
  janus64_run [h10, h8, hit'] until [Extracted.entry + 0x208]
  refine ReachesRet.done (by simp [Extracted.entry]) ?_
  have hMf : MemFrame S0.mem S0.mem (TAFL R (S0.regs 4).toNat) := MemFrame.refl _ _
  unfold Mid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  have hlt : (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0 < 2 ^ 64 := by
    rw [← hit']; simpa using Arm64.Memory.readLE_lt S0.mem (16 * i + (S0.mem.readLE descA 8 + 16)) 8
  · simp only [setRegF_apply, ite_true]; simp [wOf, htz, Nat.mod_eq_of_lt hlt]
  · simp [setRegF_apply, p1]
  · simp [setRegF_apply, p4]
  · simp [setRegF_apply, p5]
  · simp [setRegF_apply, p14]
  · simp [setRegF_apply, px]
  · simp [hdf0]
  · simp [setRegF_apply, pfs]
  · simp [pm]; exact MemFrame.refl _ _

/-- one probe step of the cache (`Format+0x23e`), the machine part: a hit (`Format+0x274`), a miss (`Format+0x25b`) or the next
entry; the three continuations are hypotheses -/
theorem step_run (impl : List Amd64.Segment) (R : IfaceModel) (tab data : BitVec 64) (S0 : State) (k : Nat) (hk64 : k ≤ 64)
    (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (S : State) (h : BitVec 64) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x23e)) (hps : PState R tab data S0 S)
    (h8 : S.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8)) (h9 : S.regs 9 = BitVec.ofNat 64 (2 ^ k - 1)) (h10 : S.regs 10 = h)
    (Q : State → Prop)
    (hhit : ∀ S' : State, (18446744073709551616 - tyOf S0 tab % 18446744073709551616 +
          Arm64.Memory.readLE S0.mem (h.toNat % 2 ^ k * 16 + (S0.mem.readLE descA 8 + 8)) 8) % 18446744073709551616 = 0 →
      S'.rip = BitVec.ofNat 64 (Extracted.entry + 0x274) → PState R tab data S0 S' →
      S'.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → (S'.regs 10).toNat = 16 * (h.toNat % 2 ^ k) →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S' Q)
    (hmiss : ∀ S' : State, S'.rip = BitVec.ofNat 64 (Extracted.entry + 0x25b) → PState R tab data S0 S' →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S' Q)
    (hrec : ∀ S' : State, ¬ Arm64.Memory.readLE S0.mem (h.toNat % 2 ^ k * 16 + (S0.mem.readLE descA 8 + 8)) 8 = 0 →
      S'.rip = BitVec.ofNat 64 (Extracted.entry + 0x23e) → PState R tab data S0 S' →
      S'.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S'.regs 9 = BitVec.ofNat 64 (2 ^ k - 1) → S'.regs 10 = h + 1#64 →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S' Q) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S Q := by
  have hand : ∀ h : BitVec 64, (h &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = h.toNat % 2 ^ k :=
    fun h => Janus.Contracts.Iface.and_mask_toNat h k hk64
  have hprobe : ∀ h : BitVec 64, ((h &&& BitVec.ofNat 64 (2 ^ k - 1)) <<< 4).toNat = 16 * (h.toNat % 2 ^ k) :=
    fun h => probeAddr h k hk64 (by omega)
  obtain ⟨p2, p1, p4, p5, p14, px, pdf, pfs, pm⟩ := hps
  janus64_run [hand] until [Extracted.entry + 0x23e, Extracted.entry + 0x25b, Extracted.entry + 0x274]
  · exact hhit _ hbr (by rfl)
      ⟨by simp [setRegF_apply, p2], by simp [setRegF_apply, p1], by simp [setRegF_apply, p4], by simp [setRegF_apply, p5],
        by simp [setRegF_apply, p14], by simpa using px, by simpa using pdf, by simpa using pfs, by simpa using pm⟩
      (by simp [setRegF_apply, h8]) (by simp only [setRegF_apply]; simpa using hprobe h)
  · exact hmiss _ (by rfl)
      ⟨by simp [setRegF_apply, p2], by simp [setRegF_apply, p1], by simp [setRegF_apply, p4],
        by simp [setRegF_apply, p5], by simp [setRegF_apply, p14], by simpa using px, by simpa using pdf, by simpa using pfs,
        by simpa using pm⟩
  · exact hrec _ hbr (by rfl)
      ⟨by simp [setRegF_apply, p2], by simp [setRegF_apply, p1], by simp [setRegF_apply, p4], by simp [setRegF_apply, p5],
        by simp [setRegF_apply, p14], by simpa using px, by simpa using pdf, by simpa using pfs, by simpa using pm⟩
      (by simp [setRegF_apply, h8]) (by simp [setRegF_apply, h9]) (by simp [setRegF_apply])

/-- one probe step of the cache (`Format+0x23e`): a hit, a miss (empty entry), or the next entry (`hrec`) -/
theorem step (impl : List Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem))
    (k : Nat) (hk64 : k ≤ 64)
    (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (S : State) (h : BitVec 64) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x23e)) (hps : PState R tab data S0 S)
    (h8 : S.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8)) (h9 : S.regs 9 = BitVec.ofNat 64 (2 ^ k - 1)) (h10 : S.regs 10 = h)
    (hrec : ∀ S' : State, taTyp S0.mem (S0.mem.readLE descA 8) (h.toNat % 2 ^ k) ≠ 0 →
      S'.rip = BitVec.ofNat 64 (Extracted.entry + 0x23e) → PState R tab data S0 S' →
      S'.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S'.regs 9 = BitVec.ofNat 64 (2 ^ k - 1) → S'.regs 10 = h + 1#64 →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S' (Mid R tab data S0)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S (Mid R tab data S0) := by
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmod := Nat.mod_lt h.toNat hN
  have htyp : ∀ i, Arm64.Memory.readLE S0.mem (i * 16 + (S0.mem.readLE descA 8 + 8)) 8 =
      taTyp S0.mem (S0.mem.readLE descA 8) i := fun i => by
    simp only [taTyp]
    rw [show S0.mem.readLE descA 8 + 8 + 16 * i = i * 16 + (S0.mem.readLE descA 8 + 8) by omega]
  have htl : tyOf S0 tab % 2 ^ 64 = tyOf S0 tab := Nat.mod_eq_of_lt (by
    have := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 8) 8; simpa [tyOf] using this)
  refine step_run impl R tab data S0 k hk64 hcb hcacc S h hpc hps h8 h9 h10 _ ?_ ?_ ?_
  · intro S' hbr hpc' hps' h8' h10'
    have h1 := Arm64.Memory.readLE_lt S0.mem (h.toNat % 2 ^ k * 16 + (S0.mem.readLE descA 8 + 8)) 8
    have h2 : tyOf S0 tab < 2 ^ 64 := by omega
    have hE : Arm64.Memory.readLE S0.mem (h.toNat % 2 ^ k * 16 + (S0.mem.readLE descA 8 + 8)) 8 = tyOf S0 tab := by
      have h1' : Arm64.Memory.readLE S0.mem (h.toNat % 2 ^ k * 16 + (S0.mem.readLE descA 8 + 8)) 8 < 2 ^ 64 := by
        simpa using h1
      rw [htl] at hbr
      omega
    exact hit impl R rt stack tab data S0 S' hpre htz k hcb hcacc hent (h.toNat % 2 ^ k) hmod
      (by rw [← htyp]; exact hE) hpc' hps' h8' h10'
  · intro S' hpc' hps'
    exact miss impl R hl H hta rt stack tab data S0 S' hpre htz hH hpc' hps'
  · intro S' hbr hpc' hps' h8' h9' h10'
    exact hrec S' (by rw [← htyp]; exact hbr) hpc' hps' h8' h9' h10'

theorem loop (impl : List Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem))
    (k : Nat) (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (j : Nat) (hj : j < 2 ^ k) (hj0 : taTyp S0.mem (S0.mem.readLE descA 8) j = 0) :
    ∀ n (S : State) (h : BitVec 64), (j + 2 ^ k - h.toNat % 2 ^ k) % 2 ^ k = n → h.toNat + n < 2 ^ 46 →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x23e) → PState R tab data S0 S →
      S.regs 8 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S.regs 9 = BitVec.ofNat 64 (2 ^ k - 1) → S.regs 10 = h →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S (Mid R tab data S0) := by
  have hk64 : k ≤ 64 := by
    refine Nat.le_of_not_lt fun hk => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 65 ≤ k by omega); omega
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc hps h8 h9 h10
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    refine step impl R hl H hta rt stack tab data S0 hpre htz hH k hk64 hcb hcacc hent S h hpc hps h8 h9 h10 ?_
    intro S' hne
    exfalso; rw [hjr, hj0] at hne; exact hne rfl
  | succ n ih =>
    intro S h hn hb' hpc hps h8 h9 h10
    refine step impl R hl H hta rt stack tab data S0 hpre htz hH k hk64 hcb hcacc hent S h hpc hps h8 h9 h10 ?_
    intro S' hne hpc' hps' h8' h9' h10'
    have hne' : h.toNat % 2 ^ k ≠ j := fun he => by rw [he, hj0] at hne; exact hne rfl
    have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    refine ih S' (h + 1#64) ?_ ?_ hpc' hps' h8' h9' h10'
    · rw [h1']; have := probe_dist (2 ^ k) j h.toNat hj hne'; omega
    · rw [h1']; omega

theorem head (impl : List Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x20)) (hpre : NilPre R rt stack tab data S0)
    (hH : tab.toNat ≠ 0 → H [descA, tyOf S0 tab] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x208)) S0 (Mid R tab data S0) := by
  have hpre' := hpre
  obtain ⟨h0', h3', h1', h5', hal, hwb, hwn, hwa, hout, hs60, hr47, hx0, hdf0, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre'
  by_cases htz : tab.toNat = 0
  · have ht : tab = 0#64 := BitVec.eq_of_toNat_eq htz
    janus64_run [h0', h3', ht] until [Extracted.entry + 0x208]
    refine ReachesRet.done (by simp [Extracted.entry]) ?_
    unfold Mid
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [wOf, h3', ht]
    · exact h1'
    all_goals first | rfl | exact hdf0.symm | exact MemFrame.refl _ _
  · have htab' := htab htz
    obtain ⟨htb, htacc, ht0, hty, hcf⟩ := htab'
    obtain ⟨hdb, hdacc, hdw, hdi, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc
    simp only [taCache] at hk hcb hcacc hcin hent hj0
    have hD : descA = 5996832 := rfl
    janus64_run [h0', h3'] until [Extracted.entry + 0x23e]
    have hk' : S0.mem.readLE (S0.mem.readLE 5996832 8) 8 = 2 ^ k - 1 := by rw [← hD]; exact hk
    have hlt4 := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 16) 4
    have hh : (BitVec.setWidth 64 (BitVec.ofNat 32 (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4))).toNat =
        Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4 := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; simp at hlt4; omega
    have hN : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmodlt := Nat.mod_lt (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4) hN
    refine loop impl R hl H hta rt stack tab data S0 hpre htz (hH htz) k hcb hcacc hent j hj hj0 _ _
      (BitVec.setWidth 64 (BitVec.ofNat 32 (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4))) rfl ?_ (by rfl)
      ⟨by simp [setRegF_apply, tyOf], by simp [setRegF_apply, h1'], by simp [setRegF_apply], by simp [setRegF_apply],
        by simp [setRegF_apply], by simp [setRegF_apply], by simp [setRegF_apply, hdf0], by simp [setRegF_apply], by simp [setRegF_apply]⟩
      (by simp [setRegF_apply, hD]) (by simp [setRegF_apply, hk']) (by simp [setRegF_apply])
    rw [hh]; simp at hlt4; omega

theorem nil_path (impl : List Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64)
    (hFp : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (FpArg data))
    (S0 : State) (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x20)) (hpre : NilPre R rt stack tab data S0)
    (hH : tab.toNat ≠ 0 → H [descA, tyOf S0 tab] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S0
      (NilQ R rt stack RFp tab data S0) := by
  obtain ⟨k, S1, hs, hr, hq⟩ := head impl R hl H hta rt stack tab data S0 hpc hpre hH
  obtain ⟨k', S', hs', hr', hq'⟩ := tail impl R rt stack RFp tab data hFp S0 S1 hr hpre hq
  exact ⟨k + k', S', hs.trans hs', hr', hq'⟩

end Fv256.Amd64.FormatNil
