import Extracted
import Fv256.SpecFormat
import Fv256.GrabRetA64

/-!
# `(*uint256.Int).Format`, path (i): the nil receiver (arm64)

From the split state `S0` at `Format+0x20` with `z == 0` (X0 = 0): `w := s.(io.Writer)` (`runtime.typeAssert`, with the inline cache probe;
a nil `s.itab` gives a nil writer), then `fmt.Fprint(w, "<nil>")` (a static `ICallContract` at `contractAddr "fmt.Fprint"`), epilogue, return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Iface
  Janus.Spec Janus.Spec.Type

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.janusRenameI false
set_option linter.unusedVariables false

open Fv256.GrabRetA64

namespace Fv256.Arm64.FormatNil

/-- the type-assertion descriptor `uint256..typeAssert.0` -/
def descA : Nat := Extracted.dataAddr.«github.com/holiman/uint256..typeAssert.0»
/-- the type descriptor of `string` (the `any` word of the argument) -/
def strTyA : Nat := Extracted.dataAddr.«type:string#f88732b8»
/-- the static string header of `"<nil>"` (the data word of the argument) -/
def hdrA : Nat := Extracted.dataAddr.«.rodata#9732ef5a»
/-- the address of the bytes `"<nil>"` (the first word of that header; the bytes themselves are not part of the extraction) -/
def litA : Nat := dataWord Extracted.program.data ".rodata+0x360c8" 0 8

/-- the itab `Type` word of the incoming `fmt.State` -/
def tyOf (S0 : State) (tab : BitVec 64) : Nat := S0.mem.readLE (tab.toNat + 8) 8

/-- the itab `getitab` answers for `s.(io.Writer)`: nil for a nil `s` -/
def wOf (R : IfaceModel) (S0 : State) (tab : BitVec 64) : Nat :=
  if tab.toNat = 0 then 0 else (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0

/-- the memory `runtime.typeAssert` may touch -/
def TAFL (R : IfaceModel) (sp : Nat) : List (Nat × Nat) :=
  R.priv ++ [(sp - R.depth, sp - 8), (sp + 8, sp + 8 + 8 * 2)] ++ [(descA, descA + 8)]

/-- the memory the whole path may touch -/
def NilFL (R : IfaceModel) (rt : List (Nat × Nat)) (sp stack : Nat) : List (Nat × Nat) :=
  rt ++ TAFL R sp ++ [(sp - stack, sp - 8), (sp + 8, sp + 8 + 8 * 5), (sp + 56, sp + 72)]

/-- the call-site property of `fmt.Fprint(w, "<nil>")` -/
def FpArg (data : BitVec 64) (sc : State) : Prop :=
  sc.regs 1 = data ∧ sc.regs 3 = 1#64 ∧ sc.regs 4 = 1#64 ∧ (sc.regs 2).toNat = sc.sp.toNat + 56 ∧
  sc.mem.readLE (sc.regs 2).toNat 8 = strTyA ∧ sc.mem.readLE ((sc.regs 2).toNat + 8) 8 = hdrA ∧
  sc.mem.readLE hdrA 8 = litA ∧ sc.mem.readLE (hdrA + 8) 8 = 5 ∧ StrOut sc.mem litA 5 Fv256.FormatSpec.nilText

/-- the precondition at `S0 = Format+0x20`, `z = 0` -/
def NilPre (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State) : Prop :=
  S0.regs 0 = 0#64 ∧ S0.regs 1 = tab ∧ S0.regs 2 = data ∧
  S0.sp.toNat % 16 = 0 ∧ 8 ≤ stack ∧ stack ≤ S0.sp.toNat ∧ S0.sp.toNat + 0x78 ≤ 2 ^ 48 ∧
  S0.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true ∧
  Outside (S0.sp.toNat - 8 - stack) (stack + 0x80) rt ∧
  S0.mem.readLE (S0.sp.toNat + 104) 8 = data.toNat ∧
  S0.mem.readLE S0.sp.toNat 8 % 4 = 0 ∧ S0.mem.readLE S0.sp.toNat 8 < 2 ^ 48 ∧
  -- the interface runtime (typeAssert): the caller's window `[sp-depth, sp+0x78)` (no push on arm64)
  CallerOK R S0 0 0x78 ∧
  TADescOK R S0.mem descA ∧ Outside descA 24 [(S0.sp.toNat - R.depth, S0.sp.toNat + 0x78)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ S0.mem.accessible tab.toNat 0x14 false = true ∧ tyOf S0 tab ≠ 0 ∧ R.IsType (tyOf S0 tab) ∧
    (taCanFail S0.mem descA = true ∨ (R.itab (taInter S0.mem descA) (tyOf S0 tab)).isSome)) ∧
  -- the literal "<nil>" and its header: read-only data, away from every written range
  S0.mem.readLE hdrA 8 = litA ∧ S0.mem.readLE (hdrA + 8) 8 = 5 ∧
  StrOut S0.mem litA 5 Fv256.FormatSpec.nilText ∧
  Outside hdrA 16 (NilFL R rt S0.sp.toNat stack) ∧ Outside litA 5 (NilFL R rt S0.sp.toNat stack)

/-- the state at `Format+0x238` (the `Fprint` setup), after the `typeAssert` part -/
def Mid (R : IfaceModel) (tab data : BitVec 64) (S0 S1 : State) : Prop :=
  (S1.regs 1).toNat = wOf R S0 tab ∧ S1.regs 2 = data ∧ S1.sp = S0.sp ∧ S1.regs 18 = S0.regs 18 ∧ S1.regs 28 = S0.regs 28 ∧
  MemFrame S0.mem S1.mem (TAFL R S0.sp.toNat)

/-- the postcondition at the return -/
def NilQ (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64) (S0 S' : State) : Prop :=
  S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
  S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
  MemFrame S0.mem S'.mem (NilFL R rt S0.sp.toNat stack) ∧
  ∃ j0 j1 j2, RFp (BitVec.ofNat 64 (wOf R S0 tab)) data (BitVec.ofNat 64 (S0.sp.toNat + 56)) 1#64 j0 j1 j2

/-- the frame of the whole path after the `Fprint` call -/
theorem frame_fp {R : IfaceModel} {rt : List (Nat × Nat)} {stack sp : Nat} {m0 m1 m : Memory} {a b : Nat}
    (mfr : MemFrame m0 m1 (TAFL R sp)) (hwb : 8 ≤ stack) (hs : stack ≤ sp)
    (hfr : MemFrame ((m1.writeLE (sp + 56) 8 a).writeLE (sp + 64) 8 b) m
      (rt ++ [(sp - stack, sp - 8), (sp + 8, sp + 8 + 8 * 5)])) :
    MemFrame m0 m (NilFL R rt sp stack) := by
  have h1 : MemFrame m0 m1 (NilFL R rt sp stack) := mfr.mono fun a n h => by
    simp only [NilFL, outside_append] at h; exact h.1.2
  have h2 : MemFrame m1 ((m1.writeLE (sp + 56) 8 a).writeLE (sp + 64) 8 b) (NilFL R rt sp stack) :=
    (((MemFrame.refl m1 _).writeLE a (r := (sp + 56, sp + 72)) (by simp [NilFL]) (by simp) (by simp)).writeLE b
      (r := (sp + 56, sp + 72)) (by simp [NilFL]) (by simp) (by simp))
  have h3 : MemFrame ((m1.writeLE (sp + 56) 8 a).writeLE (sp + 64) 8 b) m (NilFL R rt sp stack) :=
    hfr.mono fun a n h => by
      simp only [NilFL, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨h1, -⟩, h3, h4, h5⟩ := h
      refine ⟨h1, ?_, ?_⟩ <;> omega
  exact (h1.trans h2 fun a n h => ⟨h, h⟩).trans h3 fun a n h => ⟨h, h⟩

theorem tail (impl : List Segment) (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64)
    (hFp : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (FpArg data))
    (S0 S1 : State) (hpc : S1.pc = BitVec.ofNat 64 (Extracted.entry + 0x238))
    (hpre : NilPre R rt stack tab data S0) (hm : Mid R tab data S0 S1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S1
      (NilQ R rt stack RFp tab data S0) := by
  obtain ⟨h0', h1', h2', hal, h8, hsb, hwn, hwa, hout, hs104, hra4, hra48, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre
  obtain ⟨m1, m2, msp, m18, m28, mfr⟩ := hm
  have hdrL : hdrA = 0xf60c8 := rfl
  have litL : litA = 0xeaade := by decide
  simp only [hdrL, litL] at hhdr hhn hlit hho hlo
  simp only [NilFL, outside_append] at hho hlo
  obtain ⟨⟨hho1, hho2⟩, hho3⟩ := hho
  obtain ⟨⟨hlo1, hlo2⟩, hlo3⟩ := hlo
  simp only [outside_cons, outside_nil, and_true] at hho3 hlo3
  have e1 : S1.mem.readLE 0xf60c8 8 = 0xeaade := by
    rw [mfr.readLE _ _ (hho2.of_sub (by omega) (by omega))]; exact hhdr
  have e2 : S1.mem.readLE (0xf60c8 + 8) 8 = 5 := by
    rw [mfr.readLE _ _ (hho2.of_sub (by omega) (by omega))]; exact hhn
  have e3 : S1.mem.accessible 0xeaade 5 false = true := by
    rw [mfr.accessible]; exact hlit.2.2.1 (by decide)
  have e4 : strBytes S1.mem 0xeaade 5 = Fv256.FormatSpec.nilText := by
    rw [strBytes_of_frame mfr hlo2]; exact hlit.2.2.2
  have e4' : strBytes S1.mem litA 5 = Fv256.FormatSpec.nilText := by rw [litL]; exact e4
  have hT : Outside (S0.sp.toNat - 8) 16 (TAFL R S0.sp.toNat) := by
    obtain ⟨-, -, -, hd8, hdp, -, -, hc7, -⟩ := hcall
    simp only [TAFL, outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hc7.of_sub (by omega) (by omega), by omega, by omega⟩, ?_⟩
    simp only [outside_cons, outside_nil, and_true] at hdo
    omega
  have hr0 : S1.mem.readLE S0.sp.toNat 8 = S0.mem.readLE S0.sp.toNat 8 :=
    mfr.readLE _ _ (hT.of_sub (by omega) (by omega))
  have hr8 : S1.mem.readLE (S0.sp.toNat - 8) 8 = S0.mem.readLE (S0.sp.toNat - 8) 8 :=
    mfr.readLE _ _ (hT.of_sub (by omega) (by omega))
  janus_run [hr0, hr8, hra4, hra48, e1, e2, e3, e4, e4', Janus.Spec.strBytes_writeLE] calls [hFp]
  fv_ret_names_a64 junk f v m ex ep hkeep hpr hfr hR
  unfold NilQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [setReg_apply]
  · simp [setReg_apply, callRegs_apply, m28]
  · simp [setReg_apply, callRegs_apply, m18]
  · exact frame_fp mfr h8 hsb hfr
  · refine ⟨junk 0, junk 1, junk 2, ?_⟩
    have hS1 : S1.regs 1 = BitVec.ofNat 64 (wOf R S0 tab) := by rw [← m1]; simp
    have hA : S0.sp + 56#64 = BitVec.ofNat 64 (S0.sp.toNat + 56) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp
    rw [← hS1, ← hA]; exact hR

/-- the registers and memory at the `typeAssert` probe, shared by the miss, hit and loop lemmas -/
def PState (R : IfaceModel) (tab data : BitVec 64) (S0 S : State) : Prop :=
  S.regs 5 = BitVec.ofNat 64 (tyOf S0 tab) ∧ S.regs 0 = BitVec.ofNat 64 descA ∧ S.regs 2 = data ∧ S.sp = S0.sp ∧
  S.regs 28 = S0.regs 28 ∧ S.regs 18 = S0.regs 18 ∧ S.mem = S0.mem

/-- a cache miss: the call of `runtime.typeAssert` (`Format+0x294`) and the jump to `Format+0x238` -/
theorem miss (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 S : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 28).toNat S0.sp.toNat (rtView R.priv S0.mem))
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x294)) (hps : PState R tab data S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S (Mid R tab data S0) := by
  obtain ⟨h0', h1', h2', hal, h8, hsb, hwn, hwa, hout, hs104, hra4, hra48, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre
  obtain ⟨p5, p0, p2, psp, p28, p18, pm⟩ := hps
  obtain ⟨ht0, hty, hcf⟩ := htab htz |>.2.2
  have hc' := hcall
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal2, hd8, hd2, hb2, hst2, hout2, hgd, hgo⟩ := hc'
  have hD : descA = 1794272 := rfl
  have hd64 : (1794272 : Nat) % 2 ^ 64 = 1794272 := by decide
  have hdA64 : descA % 2 ^ 64 = descA := by rw [hD]
  have htl : tyOf S0 tab % 2 ^ 64 = tyOf S0 tab := Nat.mod_eq_of_lt (by
    have := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 8) 8; simpa [tyOf] using this)
  have hdo' : Outside descA 24 [(S0.sp.toNat - (R.depth + 0), S0.sp.toNat + 0x78)] := by
    simp only [outside_cons, outside_nil, and_true] at hdo ⊢; omega
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [(S0.sp.toNat - (R.depth + 0), S0.sp.toNat + 0x78)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout2 (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  janus_run until [Extracted.program.contractAddr "runtime.typeAssert"]
  have hMf : MemFrame S0.mem S0.mem [(S0.sp.toNat - (R.depth + 0), S0.sp.toNat + 0x78)] := MemFrame.refl _ _
  refine ReachesRet.call hta rfl
    ⟨RTPre.of_caller hl hcall hMf (by simp) (by simp [setReg_apply, p28]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by decide) (by decide), ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, p0, hdA64, ← hD]
    exact TADescOK.frame hdesc (MemFrame.refl _ _) hdo' hws
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, htl]; exact ht0
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, p0, htl, ← hD, hdA64]
    intro _; exact ⟨hty, hcf⟩
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, p0, htl, ← hD, hdA64, p28]
    exact hH
  · intro s' hpc' ⟨rr, v', fl, m', hs', hfr, henv', hres, hdesc2, hinter2, hcf2⟩
    subst hs'
    simp only [rtWrites, calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff,
      BitVec.toNat_ofNat, p0, hdA64, htl, ← hD] at hfr hres hdesc2 hinter2 hcf2
    janus_run until [Extracted.entry + 0x238]
    refine ReachesRet.done (by simp [Extracted.entry]) ?_
    unfold Mid
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [setReg_apply]; simp
      rw [hres.1]; simp [wOf, htz, ht0]
    · simp [setReg_apply, hs104]
    · rfl
    · simp [setReg_apply, Map.keepABI_apply, p18]
    · simp [setReg_apply, Map.keepABI_apply, p28]
    · exact hfr

/-- the entry address the probe computes in `X9` (`((h & Mask) << 4) + 8` added to the cache) -/
theorem x9_toNat (c k : Nat) (h : BitVec 64) (hk : k ≤ 64) (hc : c + 8 + 16 * 2 ^ k ≤ 2 ^ 48) :
    (BitVec.ofNat 64 c + (((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 60 &&&
      18446744073709551600#64 &&& 18446744073709551615#64) + 8#64)).toNat =
      c + (16 * (h.toNat % 2 ^ k) + 8) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  have h1 : ((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 60 &&& 18446744073709551600#64 &&&
      18446744073709551615#64).toNat = 16 * (h.toNat % 2 ^ k) := by
    rw [BitVec.toNat_and, BitVec.toNat_and, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (18446744073709551600#64).toNat = 18446744073709551600 from rfl,
      lsl4_toNat, Janus.Contracts.Iface.and_mask_toNat h k hk]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 16 * (h.toNat % 2 ^ k) + 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- a cache hit at entry `i` (`Format+0x2a8`): the cached itab is the runtime's answer -/
theorem hit (impl : List Segment) (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64)
    (S0 S : State) (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (k : Nat) (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (i : Nat) (hi : i < 2 ^ k) (hty : taTyp S0.mem (S0.mem.readLE descA 8) i = tyOf S0 tab)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x2a8)) (hps : PState R tab data S0 S)
    (h9 : (S.regs 9).toNat = S0.mem.readLE descA 8 + (16 * i + 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S (Mid R tab data S0) := by
  obtain ⟨p5, p0, p2, psp, p28, p18, pm⟩ := hps
  obtain ⟨h0', h1', h2', hal, h8, hsb, hwn, hwa, hout, hs104, hra4, hra48, hcall, hdesc, hdo, htab, -⟩ := hpre
  obtain ⟨ht0, hty0, -⟩ := htab htz |>.2.2
  have hit' : Arm64.Memory.readLE S0.mem (S0.mem.readLE descA 8 + (16 * i + 8) + 8) 8 =
      (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0 := by
    have := hent i hi (by rw [hty]; exact ht0)
    rw [hty] at this
    rw [← this]; simp only [taItab]
    rw [show S0.mem.readLE descA 8 + 16 + 16 * i = S0.mem.readLE descA 8 + (16 * i + 8) + 8 by omega]
  have hlt : (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0 < 2 ^ 64 := by
    rw [← hit']; simpa using Arm64.Memory.readLE_lt S0.mem (S0.mem.readLE descA 8 + (16 * i + 8) + 8) 8
  janus_run [h9, hit', pm] until [Extracted.entry + 0x238]
  refine ReachesRet.done (by simp [Extracted.entry]) ?_
  unfold Mid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [setReg_apply]; simp [wOf, htz, Nat.mod_eq_of_lt hlt]
  · simp [setReg_apply, p2]
  · simp [psp]
  · simp [setReg_apply, p18]
  · simp [setReg_apply, p28]
  · exact MemFrame.refl _ _

/-- one probe step of the cache (`Format+0x270`), the machine part: a hit (`Format+0x2a8`), a miss (`Format+0x294`) or the next
entry; the three continuations are hypotheses -/
theorem step_run (impl : List Segment) (R : IfaceModel) (tab data : BitVec 64) (S0 : State) (k : Nat) (hk64 : k ≤ 64)
    (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (S : State) (h : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x270)) (hps : PState R tab data S0 S)
    (h6 : S.regs 6 = BitVec.ofNat 64 (S0.mem.readLE descA 8)) (h8 : S.regs 8 = BitVec.ofNat 64 (2 ^ k - 1)) (h7 : S.regs 7 = h)
    (Q : State → Prop)
    (hhit : ∀ S' : State, S0.mem.readLE (S0.mem.readLE descA 8 + (16 * (h.toNat % 2 ^ k) + 8)) 8 = tyOf S0 tab % 18446744073709551616 →
      S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x2a8) → PState R tab data S0 S' →
      (S'.regs 9).toNat = S0.mem.readLE descA 8 + (16 * (h.toNat % 2 ^ k) + 8) →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S' Q)
    (hmiss : ∀ S' : State, S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x294) → PState R tab data S0 S' →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S' Q)
    (hrec : ∀ S' : State, ¬ Arm64.Memory.readLE S0.mem (S0.mem.readLE descA 8 + (16 * (h.toNat % 2 ^ k) + 8)) 8 = 0 →
      S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x270) → PState R tab data S0 S' →
      S'.regs 6 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S'.regs 8 = BitVec.ofNat 64 (2 ^ k - 1) → S'.regs 7 = h + 1#64 →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S' Q) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S Q := by
  have hand : ∀ h : BitVec 64, (h &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = h.toNat % 2 ^ k :=
    fun h => Janus.Contracts.Iface.and_mask_toNat h k hk64
  obtain ⟨p5, p0, p2, psp, p28, p18, pm⟩ := hps
  have hc9 : ∀ h : BitVec 64, (BitVec.ofNat 64 (S0.mem.readLE descA 8) + (((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 60 &&&
      18446744073709551600#64 &&& 18446744073709551615#64) + 8#64)).toNat = S0.mem.readLE descA 8 + (16 * (h.toNat % 2 ^ k) + 8) :=
    fun h => x9_toNat _ _ h hk64 hcb
  janus_run [hand] until [Extracted.entry + 0x270, Extracted.entry + 0x294, Extracted.entry + 0x2a8]
  · exact hhit _ hbr (by rfl)
      ⟨by simp [setReg_apply, p5], by simp [setReg_apply, p0], by simp [setReg_apply, p2], by simp [psp], by simp [setReg_apply, p28],
        by simp [setReg_apply, p18], by simpa using pm⟩
      (by simp only [setReg_apply]; simpa using hc9 h)
  · exact hmiss _ (by rfl)
      ⟨by simp [setReg_apply, p5], by simp [setReg_apply, p0], by simp [setReg_apply, p2], by simp [psp], by simp [setReg_apply, p28],
        by simp [setReg_apply, p18], by simpa using pm⟩
  · exact hrec _ hbr (by rfl)
      ⟨by simp [setReg_apply, p5], by simp [setReg_apply, p0], by simp [setReg_apply, p2], by simp [psp], by simp [setReg_apply, p28],
        by simp [setReg_apply, p18], by simpa using pm⟩
      (by simp [setReg_apply, h6]) (by simp [setReg_apply, h8]) (by simp [setReg_apply])

/-- one probe step of the cache (`Format+0x270`): a hit, a miss (empty entry), or the next entry (`hrec`) -/
theorem step (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 28).toNat S0.sp.toNat (rtView R.priv S0.mem))
    (k : Nat) (hk64 : k ≤ 64)
    (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (S : State) (h : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x270)) (hps : PState R tab data S0 S)
    (h6 : S.regs 6 = BitVec.ofNat 64 (S0.mem.readLE descA 8)) (h8 : S.regs 8 = BitVec.ofNat 64 (2 ^ k - 1)) (h7 : S.regs 7 = h)
    (hrec : ∀ S' : State, taTyp S0.mem (S0.mem.readLE descA 8) (h.toNat % 2 ^ k) ≠ 0 →
      S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x270) → PState R tab data S0 S' →
      S'.regs 6 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S'.regs 8 = BitVec.ofNat 64 (2 ^ k - 1) → S'.regs 7 = h + 1#64 →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S' (Mid R tab data S0)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S (Mid R tab data S0) := by
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmod := Nat.mod_lt h.toNat hN
  have htyp : taTyp S0.mem (S0.mem.readLE descA 8) (h.toNat % 2 ^ k) =
      Arm64.Memory.readLE S0.mem (S0.mem.readLE descA 8 + (16 * (h.toNat % 2 ^ k) + 8)) 8 := by
    simp only [taTyp]; congr 1; omega
  have htl : tyOf S0 tab % 2 ^ 64 = tyOf S0 tab := Nat.mod_eq_of_lt (by
    have := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 8) 8; simpa [tyOf] using this)
  refine step_run impl R tab data S0 k hk64 hcb hcacc S h hpc hps h6 h8 h7 _ ?_ ?_ ?_
  · intro S' hbr hpc' hps' h9'
    rw [htl] at hbr
    exact hit impl R rt stack tab data S0 S' hpre htz k hcb hcacc hent (h.toNat % 2 ^ k) hmod
      (by rw [htyp]; exact hbr) hpc' hps' h9'
  · intro S' hpc' hps'
    exact miss impl R hl H hta rt stack tab data S0 S' hpre htz hH hpc' hps'
  · intro S' hbr hpc' hps' h6' h8' h7'
    exact hrec S' (by rw [htyp]; exact hbr) hpc' hps' h6' h8' h7'

theorem loop (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpre : NilPre R rt stack tab data S0) (htz : tab.toNat ≠ 0)
    (hH : H [descA, tyOf S0 tab] (S0.regs 28).toNat S0.sp.toNat (rtView R.priv S0.mem))
    (k : Nat) (hcb : S0.mem.readLE descA 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : S0.mem.accessible (S0.mem.readLE descA 8) (8 + 16 * 2 ^ k) false = true)
    (hent : ∀ i, i < 2 ^ k → taTyp S0.mem (S0.mem.readLE descA 8) i ≠ 0 →
      taItab S0.mem (S0.mem.readLE descA 8) i = (R.itab (taInter S0.mem descA) (taTyp S0.mem (S0.mem.readLE descA 8) i)).getD 0)
    (j : Nat) (hj : j < 2 ^ k) (hj0 : taTyp S0.mem (S0.mem.readLE descA 8) j = 0) :
    ∀ n (S : State) (h : BitVec 64), (j + 2 ^ k - h.toNat % 2 ^ k) % 2 ^ k = n → h.toNat + n < 2 ^ 46 →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x270) → PState R tab data S0 S →
      S.regs 6 = BitVec.ofNat 64 (S0.mem.readLE descA 8) → S.regs 8 = BitVec.ofNat 64 (2 ^ k - 1) → S.regs 7 = h →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S (Mid R tab data S0) := by
  have hk64 : k ≤ 64 := by
    refine Nat.le_of_not_lt fun hk => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 65 ≤ k by omega); omega
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc hps h6 h8 h7
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    refine step impl R hl H hta rt stack tab data S0 hpre htz hH k hk64 hcb hcacc hent S h hpc hps h6 h8 h7 ?_
    intro S' hne
    exfalso; rw [hjr, hj0] at hne; exact hne rfl
  | succ n ih =>
    intro S h hn hb' hpc hps h6 h8 h7
    refine step impl R hl H hta rt stack tab data S0 hpre htz hH k hk64 hcb hcacc hent S h hpc hps h6 h8 h7 ?_
    intro S' hne hpc' hps' h6' h8' h7'
    have hne' : h.toNat % 2 ^ k ≠ j := fun he => by rw [he, hj0] at hne; exact hne rfl
    have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    refine ih S' (h + 1#64) ?_ ?_ hpc' hps' h6' h8' h7'
    · rw [h1']; have := probe_dist (2 ^ k) j h.toNat hj hne'; omega
    · rw [h1']; omega

theorem head (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (tab data : BitVec 64) (S0 : State)
    (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x20)) (hpre : NilPre R rt stack tab data S0)
    (hH : tab.toNat ≠ 0 → H [descA, tyOf S0 tab] (S0.regs 28).toNat S0.sp.toNat (rtView R.priv S0.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x238)) S0 (Mid R tab data S0) := by
  have hpre' := hpre
  obtain ⟨h0', h1', h2', hal, h8, hsb, hwn, hwa, hout, hs104, hra4, hra48, hcall, hdesc, hdo, htab, hhdr, hhn, hlit, hho, hlo⟩ := hpre'
  by_cases htz : tab.toNat = 0
  · have ht : tab = 0#64 := BitVec.eq_of_toNat_eq htz
    janus_run [h0', h1', ht] until [Extracted.entry + 0x238]
    refine ReachesRet.done (by simp [Extracted.entry]) ?_
    unfold Mid
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [wOf, h1', ht]
    · exact h2'
    all_goals first | rfl | exact MemFrame.refl _ _
  · have htab' := htab htz
    obtain ⟨htb, htacc, ht0, hty, hcf⟩ := htab'
    obtain ⟨hdb, hdacc, hdw, hdi, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc
    simp only [taCache] at hk hcb hcacc hcin hent hj0
    have hD : descA = 1794272 := rfl
    janus_run [h0', h1'] until [Extracted.entry + 0x270]
    have hk' : S0.mem.readLE (S0.mem.readLE 1794272 8) 8 = 2 ^ k - 1 := by rw [← hD]; exact hk
    have hlt4 := Arm64.Memory.readLE_lt S0.mem (tab.toNat + 16) 4
    have hh : (BitVec.ofNat 64 (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4)).toNat =
        Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4 := by
      simp only [BitVec.toNat_ofNat]; simp at hlt4; omega
    have hN : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmodlt := Nat.mod_lt (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4) hN
    refine loop impl R hl H hta rt stack tab data S0 hpre htz (hH htz) k hcb hcacc hent j hj hj0 _ _
      (BitVec.ofNat 64 (Arm64.Memory.readLE S0.mem (tab.toNat + 16) 4)) rfl ?_ (by rfl)
      ⟨by simp [setReg_apply, tyOf], by simp [setReg_apply, hD], by simp [setReg_apply, h2'], by simp, by simp [setReg_apply],
        by simp [setReg_apply], by simp⟩
      (by simp [setReg_apply, hD]) (by simp [setReg_apply, hk']) (by simp [setReg_apply])
    rw [hh]; simp at hlt4; omega

theorem nil_path (impl : List Segment) (R : IfaceModel) (hl : R.Laws) (H : RtReady)
    (hta : TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64)
    (hFp : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (FpArg data))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x20)) (hpre : NilPre R rt stack tab data S0)
    (hH : tab.toNat ≠ 0 → H [descA, tyOf S0 tab] (S0.regs 28).toNat S0.sp.toNat (rtView R.priv S0.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S0
      (NilQ R rt stack RFp tab data S0) := by
  obtain ⟨k, S1, hs, hr, hq⟩ := head impl R hl H hta rt stack tab data S0 hpc hpre hH
  obtain ⟨k', S', hs', hr', hq'⟩ := tail impl R rt stack RFp tab data hFp S0 S1 hr hpre hq
  exact ⟨k + k', S', hs.trans hs', hr', hq'⟩

end Fv256.Arm64.FormatNil
