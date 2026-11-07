import Extracted
import Fv256.Arm64.FormatCS
import Fv256.SpecFormat
import Fv256.Arm64.SegCompose
import Fv256.Arm64.SummaryEnsures
import Fv256.IntoBigCommon
import Fv256.Arm64.FormatPrefix
import Fv256.Arm64.FormatNil
import Fv256.Arm64.FormatFastAll
import Fv256.Arm64.FormatFastBig
import Fv256.Arm64.FormatFastHexSum
import Fv256.Arm64.FormatTransfer
import Fv256.Arm64.FormatWitB
import Fv256.Arm64.FormatWitN
import Fv256.Arm64.FormatWitG
import Fv256.Arm64.FormatInhabit
import Fv256.Arm64.FormatInhabitNil

/-!
# `(*uint256.Int).Format(s fmt.State, ch rune)` (arm64): the assembly

Entry: `prefix_nz` / `prefix_z` (prologue, spills) to `Format+0x44` / `Format+0x20`, then the nil path (`FormatNil.nil_path`), or the fast path
(`FormatFast.fast_arm64`, two exits), whose second exit enters the big path (`FormatFast.big_path`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Fv256.FormatFastA64 Fv256.Arm64.FormatTransfer Fv256.Arm64.FormatFast
open Janus.Spec.Type (IfaceModel)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Fv256.Arm64.Format

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

theorem correctness (impl : List Janus.Segment) (hI : ImplApart Extracted.program impl)
    (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hta : Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (R2 : RtInv)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat))
    (hss : RtContract (Extracted.program.ofImpl impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hst : RtContract (Extracted.program.ofImpl impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (fW fP fF fWr stack b0 zv : Nat) (RW RP RF RWr RFp RBf : Res)
    (h4608 : 4608 ≤ stack)
    (z tab data ch : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True) (RtPreserves R2))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True) (RtPreserves R2))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes zv (ch.toNat % 2 ^ 32))))
    (hFp : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (Fv256.Arm64.FormatNil.FpArg data))
    (hBf : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 120 rt (fun _ => [])
      RBf (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P zv ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, data, ch]
      (PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data)
      (fun s s' =>
        (z.toNat = 0 → NilPost R rt stack RFp tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt stack fW fP fF RW RP RF RWr data ch s s' ∨
          BigPost R2 rt stack fW fP fF RW RP RF RBf tab data ch s s')) := by
  have hcP : RtContract (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») :=
    RtContract.of_codeIn (codeIn_ofImpl_restrict_of_apart hI [nmHex]) hss
  have hcL : RtContract (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») :=
    RtContract.of_codeIn (codeIn_ofImpl_of_apart hI) hss
  have hc2L : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec :=
    RtContract.of_codeIn (codeIn_ofImpl_of_apart hI) hst
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary
    (PRE := PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data)
    (POST := fun s s' =>
        (z.toNat = 0 → NilPost R rt stack RFp tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt stack fW fP fF RW RP RF RWr data ch s s' ∨
          BigPost R2 rt stack fW fP fF RW RP RF RBf tab data ch s s'))
    (pre := fun s => ∃ ret, RetAddr (Extracted.program.link impl) ret ∧
      CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
      PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data s)
    (post := fun s s' => ABIReturn s s' ∧ _) ?_ (fun ret hret s hs hp => ⟨ret, hret, hs, hp⟩) (fun _ _ _ _ _ _ h => h)
  intro s hpc ⟨ret, hret, hs, hpre⟩
  obtain ⟨⟨hrt32, hdrt, ht1, ht2, ht3⟩, hc, hnil, hfast⟩ := hpre
  have hr0 : s.regs 0 = z := hs.args 0 (by simp)
  have hr1 : s.regs 1 = tab := hs.args 1 (by simp)
  have hr2 : s.regs 2 = data := hs.args 2 (by simp)
  have hr3 : s.regs 3 = ch := hs.args 3 (by simp)
  have hlr : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
  have hr30 : (s.regs 30).toNat = ret := by
    rw [hlr, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hret.user; omega)
  have hl4 : (s.regs 30).toNat % 4 = 0 := by rw [hr30]; exact hret.aligned
  have hl48 : (s.regs 30).toNat < 2 ^ 48 := by rw [hr30]; exact hret.user
  have hcP' : PreCommon rt stack s := hc
  obtain ⟨hg, hal, hstk, hhi, hacc, hout⟩ := hc
  have h8 : 8 ≤ stack := by omega
  have hgoal : (BitVec.ofNat 64 ret : BitVec 64) = s.regs GoABI.regLR := by rw [hlr]
  show ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s _
  rw [← hgoal]
  by_cases hz : z.toNat = 0
  · obtain ⟨hn, hH⟩ := hnil hz
    have P1 := FormatPrefix.prefix_z impl rt stack z tab data ch s hpc hr0 hr1 hr2 hr3 hz hg hal hstk hhi hacc
    refine Fv256.Arm64.SegCompose.seg_trans P1 (fun S0 hr hq => ?_)
    obtain ⟨hz0, hz1, hz2, hz3, hsp, h29, h28, h18, h96, h104, hra, hrfp, hfr, hreg⟩ := hq
    have hrn := sp0_toNat (s := s) (by omega) hsp
    have hz0' : S0.regs 0 = 0#64 := by rw [hz0]; exact BitVec.eq_of_toNat_eq (by simpa using hz)
    have hnp := nilpre_of hl hcP' hn h8 hz0' hz1 hz2 hsp h28 h104 hra hl4 hl48 hfr
    have hco := hn.1
    have hws := priv_out hco
    have hd8 : 8 ≤ R.depth := hco.2.2.2.1
    have hdo' : Outside Fv256.Arm64.FormatNil.descA 24 (PFL s.sp.toNat) := by
      have := hn.2.2.1
      simp only [outside_cons, outside_nil, and_true] at this; rw [pfl_out]; omega
    have hty : tab.toNat ≠ 0 → Fv256.Arm64.FormatNil.tyOf S0 tab = Fv256.Arm64.FormatNil.tyOf s tab := fun h => by
      unfold Fv256.Arm64.FormatNil.tyOf; exact hfr.readLE _ _ (hn.2.2.2.1 h).2.2.2.2.2
    have hH' : tab.toNat ≠ 0 → H [Fv256.Arm64.FormatNil.descA, Fv256.Arm64.FormatNil.tyOf S0 tab] (S0.regs 28).toNat
        S0.sp.toNat (rtView R.priv S0.mem) := fun h => by
      rw [hty h, h28, hrn, rtView_frame hreg (fun a hin => bytes_frame hfr (hws a 1 hin))]
      exact hH h
    have hnil := Fv256.Arm64.FormatNil.nil_path impl R hl H hta rt stack RFp tab data hFp S0 hr hnp hH'
    have hra' : S0.mem.readLE S0.sp.toNat 8 = ret := by rw [hrn, hra, hr30]
    rw [hra'] at hnil
    refine Fv256.Arm64.SegCompose.seg_mono hnil (fun S' hq' => ⟨abi_of (by omega) hsp hrfp h28 h18 hq'.1 hq'.2.1 hq'.2.2.1 hq'.2.2.2.1,
      fun _ => ?_, fun h => absurd hz h⟩)
    have hfrm := hq'.2.2.2.2.1
    rw [hrn] at hfrm
    obtain ⟨j0, j1, j2, hR⟩ := hq'.2.2.2.2.2
    rw [wOf_frame (R := R) hfr hdo' (fun h => (hn.2.2.2.1 h).2.2.2.2.2), hrn] at hR
    refine ⟨hfr.trans hfrm (fun a n h => ?_), j0, j1, j2, hR⟩
    simp only [NilFLE, outside_append] at h
    exact ⟨h.2, h.1⟩
  · obtain ⟨hf, hx, hzv, hinv, hbig⟩ := hfast hz
    have hf0 := hf
    have P1 := FormatPrefix.prefix_nz impl rt stack z tab data ch s hpc hr0 hr1 hr2 hr3 hz hg hal hstk hhi hacc
    refine Fv256.Arm64.SegCompose.seg_trans P1 (fun S0 hr hq => ?_)
    obtain ⟨hz0, hz1, hz2, hz3, hsp, h29, h28, h18, h96, h104, hra, hrfp, hfr, hreg⟩ := hq
    have hrn := sp0_toNat (s := s) (by omega) hsp
    have hfpre := fpre_of hcP' hf h8 hz0 hz1 hz2 hsp h29 h96 h104 hfr
    obtain ⟨xdl, xg, xgo, xgd, xH⟩ := fx_of hcP' hf hx hsp h28 hfr hreg
    obtain ⟨xH1, xH2, xH3, xH4, xH5⟩ := xH
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzd⟩ := hf0
    have hzv0 : val256 S0.mem z.toNat = zv := by
      show S0.mem.readLE z.toNat 32 = zv
      rw [rdW (stack := stack) hfr hzd]; exact hzv
    have hWr' : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
        (FastWP data (Fv256.FormatSpec.fastBytes (val256 S0.mem z.toNat) ((S0.regs 3).toNat % 2 ^ 32))) := by
      rw [hzv0, hz3]; exact hWr
    have hra' : S0.mem.readLE S0.sp.toNat 8 = ret := by rw [hrn, hra, hr30]
    have hret' : CodePtrOK (S0.mem.readLE S0.sp.toNat 8) := by
      rw [hra']; exact ⟨hret.aligned, by have := hret.user; omega⟩
    obtain ⟨hgr, hfl, hbt, hat, hok1, hok2, hok3, hok4, hbud, hwin, hzR⟩ := hbig
    have hwR : Outside (S0.sp.toNat - stack) (stack + 0x78) R2.rt := by
      rw [hrn]; exact hwin.of_sub (by omega) (by omega)
    have hg688 : GuardOK S0 688 := by
      obtain ⟨g1, g2, g3⟩ := xg
      exact ⟨g1, g2, by omega⟩
    have hrt := fast_arm64 impl R2 rt H stack fW fP fF fWr RW RP RF RWr z tab data hI hW hP hF S0 hWr' hcL hcP hc2L hrt32 hr hfpre hwR
      h4608 xdl hdrt ht1 ht2 ht3 hg688 xgo xgd xH1 xH2 xH3 xH4 xH5 hret'
    obtain ⟨k, S', hsteps, t, ht, hrip', hq'⟩ := hrt
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rw [hra'] at hrip'
      obtain ⟨⟨⟨e4, e29, e28, e18, hfrm, hwr⟩, hph, hch⟩, hreg'⟩ := hq'
      refine ⟨k, S', hsteps, hrip', ?_⟩
      rw [hz3] at hch
      rw [hrn] at hfrm
      refine ⟨abi_of (by omega) hsp hrfp h28 h18 e4 e29 e28 e18, fun h => absurd h hz, fun _ => Or.inl ?_⟩
      refine ⟨hfr.trans hfrm (fun a n h => ?_), hwr, hph, hch⟩
      simp only [outside_append] at h
      exact ⟨h.2, h.1⟩
    · obtain ⟨⟨hfi, hk, hnp⟩, hreg'⟩ := hq'
      rw [hz3] at hnp
      have hfi' : FInv rt stack z tab data (ch.toNat % 2 ^ 32) S0 S' := by rw [hz3] at hfi; exact hfi
      obtain ⟨i4, i29, i28, i18, hfrm, i88, i96, i104, i112⟩ := hfi'
      have hinv0 : R2.inv b0 [] (S0.regs 28).toNat (view R2.rt [] S0.mem) := by
        rw [h28, view_frame hfr hreg hstk hwin]; exact hinv
      have hinv1 : R2.inv b0 [] (S'.regs 28).toNat (view R2.rt [] S'.mem) := by rw [i28]; exact hk b0 [] hinv0
      have hBf' : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 120 rt
          (fun _ => []) RBf (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P (val256 S0.mem z.toNat) ∧
            sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) := by
        rw [hzv0]; exact hBf
      have hwa0 : S0.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true := hfpre.2.2.2.2.2.2.2.2.1
      have hdl' : Extracted.program.DataLoaded S'.mem := by
        refine dataLoaded_frame xdl hreg' hfrm (fun d hd => ?_)
        have hdisj := dataLoaded_disjoint xdl hd hwa0
        exact out_fl (hdrt d hd) (by omega) (by omega)
      obtain ⟨g1, g2, g3⟩ := xg
      have hgrd : S'.mem.readLE ((S0.regs 28).toNat + 16) 8 = S0.mem.readLE ((S0.regs 28).toNat + 16) 8 :=
        hfrm.readLE _ _ (out_fl xgo (by omega) (by omega))
      have hg' : GuardOK S' 4144 := by
        refine ⟨by rw [i28]; exact g1, by rw [i28, hfrm.accessible]; exact g2, ?_⟩
        rw [i28, hgrd, i4]; exact g3
      have hflag : S'.mem.accessible Fv256.Arm64.IntoBig.flagAddr 4 false = true := by
        rw [hfrm.accessible, hfr.accessible]; exact hfl
      have hoF : Outside (S0.sp.toNat - 8) 128 rt := by
        rw [hrn]; exact hout.of_sub (by omega) (by omega)
      obtain ⟨k2, S2, hs2, hr2, hq2⟩ := big_path impl hI R2 b0 hnew hwb1 hwb2 rt rt stack fW fP fF fWr RBf z tab data
        (ch.toNat % 2 ^ 32) S0 S' hBf' hrip' hfpre ⟨i4, i29, i28, i18, hfrm, i88, i96, i104, i112⟩ (Nat.mod_lt _ (by decide)) h4608 hz hdl'
        hg' (by rw [i28]; exact xgd) (by rw [i28, h28]; exact hgr) hflag hbt hat hok1 hok2 hok3 hok4 hinv1 hbud hwR hzR hoF hret'
      rw [hra'] at hr2
      refine ⟨k + k2, S2, hsteps.trans hs2, hr2, ?_⟩
      obtain ⟨b4, b29, b28, b18, bfr, bP⟩ := hq2
      rw [hrn] at hfrm bfr
      refine ⟨abi_of (by omega) hsp hrfp h28 h18 b4 b29 (b28.trans i28) (b18.trans i18), fun h => absurd h hz, fun _ => Or.inr ?_⟩
      refine ⟨hfr.trans (hfrm.trans bfr (fun a n h => ?_)) (fun a n h => ⟨(bigfl_sub hstk h).1, h⟩), hnp, bP⟩
      have hh := bigfl_sub hstk h
      refine ⟨hh.2.1, ?_⟩
      have h3 := hh.2.2
      simp only [outside_append, outside_cons, outside_nil, and_true] at h3 ⊢
      obtain ⟨⟨h1, h2⟩, h4, h5⟩ := h3
      exact ⟨⟨h1, h2⟩, by omega, by omega⟩

namespace Witness

/-- The fast path (`z = 16`, verb `d`, every query answered plain): all hypotheses of `correctness`, the toy runtime and callees, and the
precondition hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (Fv256.Arm64.FormatNil.FpArg data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt 4608 0x400 fa fa fa fa 16 z tab data s ) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (z.toNat = 0 → NilPost R rt 4608 Rd tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt 4608 fa fa fa Rc Rc Rc Rc data ch s s' ∨
          BigPost R2 rt 4608 fa fa fa Rc Rc Rc Rd tab data ch s s') := by
  obtain ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ⟨h10, h11, h12, h13, h14, h15, hret, hsetup, hp16⟩, hcs⟩ := Fv256.Arm64.FormatWitB.nonvacuous_core
  exact ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ⟨h10, h11, h12, h13, h14, h15, hret, hsetup, hp16⟩, hcs,
    correctness impl h1 R h2 H h3 R2 h4 h5 h6 rt h7 h8 (fa) (fa) (fa) (fa) (4608) (0x400) (16) (Rc) (Rc) (Rc) (Rc) (Rd) (Rd) h9 z tab data ch h10 h11 h12 h13 h14 h15 ret hret s hsetup hp16⟩


/-- The nil receiver (`z = 0`). -/
theorem nil : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (Fv256.Arm64.FormatNil.FpArg data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt 4608 0x400 fa fa fa fa 0 z tab data s ) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (z.toNat = 0 → NilPost R rt 4608 Rd tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt 4608 fa fa fa Rc Rc Rc Rc data ch s s' ∨
          BigPost R2 rt 4608 fa fa fa Rc Rc Rc Rd tab data ch s s') := by
  obtain ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ⟨h10, h11, h12, h13, h14, h15, hret, hsetup, hp16⟩, hcs⟩ := Fv256.Arm64.FormatWitN.nil_core
  exact ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ⟨h10, h11, h12, h13, h14, h15, hret, hsetup, hp16⟩, hcs,
    correctness impl h1 R h2 H h3 R2 h4 h5 h6 rt h7 h8 (fa) (fa) (fa) (fa) (4608) (0x400) (0) (Rc) (Rc) (Rc) (Rc) (Rd) (Rd) h9 z tab data ch h10 h11 h12 h13 h14 h15 ret hret s hsetup hp16⟩


/-- The big path (`z = 16`, the callees answer "has width"): the toy allocator `R2` is satisfiable and serves `IntoBig`'s requests. -/
theorem big : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608 ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (Fv256.Arm64.FormatNil.FpArg data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt 4608 0x400 fa fa fa fa 16 z tab data s ∧
    NotPlain Rc Rc Rc data fa fa fa ch (ch.toNat % 2 ^ 32) ∧
    (∃ (P : Nat) (j0 j1 j2 : BitVec 64), Rd (BitVec.ofNat 64 P) tab data
      (BitVec.ofNat 64 (if ch.toNat % 2 ^ 32 < 2 ^ 31 then ch.toNat % 2 ^ 32 else ch.toNat % 2 ^ 32 + 18446744069414584320)) j0 j1 j2) ) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (z.toNat = 0 → NilPost R rt 4608 Rd tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt 4608 fa fa fa Rc Rc Rc Rc data ch s s' ∨
          BigPost R2 rt 4608 fa fa fa Rc Rc Rc Rd tab data ch s s') := by
  obtain ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11, h12, h13, h14, h15, hret, hsetup, hp16, hp17, hp18⟩, hcs⟩ := Fv256.Arm64.FormatWitG.big_core
  exact ⟨impl, R, H, R2, rt, fa, Rc, Rd, z, tab, data, ch, ret, s, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h11, h12, h13, h14, h15, hret, hsetup, hp16, hp17, hp18⟩, hcs,
    correctness impl h1 R h2 H h3 R2 h4 h5 h6 rt h7 h8 (fa) (fa) (fa) (fa) (4608) (0x400) (16) (Rc) (Rc) (Rc) (Rc) (Rd) (Rd) h9 z tab data ch h10 h11 h12 h13 h14 h15 ret hret s hsetup hp16⟩

end Witness

end Fv256.Arm64.Format
