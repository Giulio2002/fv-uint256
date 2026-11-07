import Extracted
import Fv256.SpecFormat
import Fv256.SegCompose
import Fv256.UtilE
import Fv256.IntoBigCommon
import Fv256.Amd64.FormatPrefix
import Fv256.Amd64.FormatNil
import Fv256.Amd64.FormatFastAll
import Fv256.Amd64.FormatTransfer
import Fv256.Amd64.FormatFastHexSum

/-!
# `(*uint256.Int).Format(s fmt.State, ch rune)` (amd64): the assembly

Entry: `prefix_nz` / `prefix_z` (prologue, spills) to `Format+0x45` / `Format+0x20`, then the nil path (`FormatNil.nil_path`), or the fast path
(`FormatFast.fast_amd64`, two exits), whose second exit enters the big path (iii), taken here as the explicit hypothesis `hbig`
(the engine worker's lemma) and the named assumption `CalleePreservesRt R2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Fv256.FormatFast Fv256.Amd64.FormatTransfer Fv256.Amd64.FormatFast
open Janus.Spec.Type (IfaceModel)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Fv256.Amd64.Format

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

theorem correctness (impl : List Janus.Amd64.Segment) (hI : ImplApart Extracted.program impl)
    (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hta : Janus.Contracts.IfaceAmd64.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (R2 : RtInv)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat))
    (hss : RtContract64 (Extracted.program.ofImpl impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hst : RtContract64 (Extracted.program.ofImpl impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (fW fP fF fWr stack b0 zv : Nat) (RW RP RF RWr RFp RBf : Res)
    (h4568 : 4568 ≤ stack)
    (z tab data ch : BitVec 64)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2))
    (hP : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2))
    (hF : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes zv (ch.toNat % 2 ^ 32))))
    (hFp : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (Fv256.Amd64.FormatNil.FpArg data))
    (hBf : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => [])
      RBf (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat zv ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32))
    (hbig : ∀ S0 S : State, z.toNat ≠ 0 → FPre rt stack z tab data fW fP fF fWr S0 → S0.mem.readLE z.toNat 32 = zv →
      NotPlain RW RP RF data tab ch fP fF (ch.toNat % 2 ^ 32) →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x1cc) → FInv rt stack z tab data (ch.toNat % 2 ^ 32) S0 S →
      R2.inv b0 [] (S.regs 14).toNat (view R2.rt [] S.mem) →
      ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
        (BigQ R2 rt stack RBf tab data ch S0)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, data, ch]
      (PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data)
      (fun s s' =>
        (z.toNat = 0 → NilPost R rt stack RFp tab data s s') ∧
        (z.toNat ≠ 0 → FastPost rt stack fP fF RW RP RF RWr tab data ch s s' ∨
          BigPost R2 rt stack fP fF RW RP RF RBf tab data ch s s')) := by
  have hcP : RtContract64 (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») :=
    RtContract64.of_codeIn (codeIn_ofImpl_restrict_of_apart64 hI [nmHex]) hss
  have hcL : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») :=
    RtContract64.of_codeIn (codeIn_ofImpl_of_apart64 hI) hss
  have hc2L : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec :=
    RtContract64.of_codeIn (codeIn_ofImpl_of_apart64 hI) hst
  refine Fv256.E.ensures_of_summary64 (spre := fun s => ∃ ret, RetAddr (Extracted.program.link impl) ret ∧
      CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
      PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data s)
    (Q := fun s s' => ABIReturn s s' ∧ _) ?_ (fun ret s hret hs hp => ⟨ret, hret, hs, hp⟩) (fun _ _ _ _ _ _ h => h)
  intro s hrip ⟨ret, hret, hs, hpre⟩
  obtain ⟨⟨hrt32, hdrt, ht1, ht2, ht3⟩, hc, hnil, hfast⟩ := hpre
  have hr0 : s.regs 0 = z := hs.args 0 (by simp)
  have hr3 : s.regs 3 = tab := hs.args 1 (by simp)
  have hr1 : s.regs 1 = data := hs.args 2 (by simp)
  have hr7 : s.regs 7 = ch := hs.args 3 (by simp)
  have hretv : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := by
    rw [hs.ret]; exact hret.user
  have hx0 : s.xmm 15 = 0 := hs.zero
  have hdf0 : s.df = false := hs.df
  obtain ⟨hg, hal, hstk, hhi, hacc, hout⟩ := hc
  have hc' : PreCommon rt stack s := ⟨hg, hal, hstk, hhi, hacc, hout⟩
  by_cases hz : z.toNat = 0
  · obtain ⟨hn, hH⟩ := hnil hz
    have P1 := FormatPrefix.prefix_z impl rt stack fW fP fF fWr z tab data ch s hrip hr0 hr3 hr1 hr7 hz hg hal hstk hhi hacc hout
    refine Fv256.SegCompose.seg_trans P1 (fun S0 hr hq => ?_)
    obtain ⟨hz0, hz3, hz1, hz7, hrs4, hrs5, hr14, hxmm, hdf, hfs, h58, h60, hfr, hrbp, hreg⟩ := hq
    have hrn := rsp0_toNat (s := s) (by omega) hrs4
    have hz0' : S0.regs 0 = 0#64 := by rw [hz0]; exact BitVec.eq_of_toNat_eq (by simpa using hz)
    have hnp := nilpre_of hl hc' hn hz0' hz3 hz1 hrs4 hrs5 hr14 hxmm hdf hx0 hdf0 hretv h60 hfr
    have hco := hn.1
    have hws := priv_out hco
    have hdo' : Outside Fv256.Amd64.FormatNil.descA 24 (PFL (s.regs 4).toNat) := by
      have := hn.2.2.1
      simp only [outside_cons, outside_nil, and_true] at this; rw [pfl_out]; omega
    have hty : tab.toNat ≠ 0 → Fv256.Amd64.FormatNil.tyOf S0 tab = Fv256.Amd64.FormatNil.tyOf s tab := fun h => by
      unfold Fv256.Amd64.FormatNil.tyOf; exact hfr.readLE _ _ (hn.2.2.2.1 h).2.2.2.2.2
    have hH' : tab.toNat ≠ 0 → H [Fv256.Amd64.FormatNil.descA, Fv256.Amd64.FormatNil.tyOf S0 tab] (S0.regs 14).toNat
        ((S0.regs 4).toNat - 8) (rtView R.priv S0.mem) := fun h => by
      rw [hty h, hr14, hrn, rtView_frame hreg (fun a hin => bytes_frame hfr (hws a 1 hin)),
        show (s.regs 4).toNat - 72 - 8 = (s.regs 4).toNat - 80 by omega]
      exact hH h
    have hra : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [hrn, show (s.regs 4).toNat - 72 + 72 = (s.regs 4).toNat by omega]
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hnil := Fv256.Amd64.FormatNil.nil_path impl R hl H hta rt stack RFp tab data hFp S0 hr hnp hH'
    rw [retAddrOf_eq, ← hra]
    refine ReachesRet.mono hnil (fun S' hq' => ⟨abi_of (by omega) hrs4 hrbp hr14 hxmm hq'.1 hq'.2.1 hq'.2.2.1 hq'.2.2.2.1,
      fun _ => ?_, fun h => absurd hz h⟩)
    have hfrm := hq'.2.2.2.2.2.2.1
    rw [hrn] at hfrm
    obtain ⟨j0, j3, j1, hR⟩ := hq'.2.2.2.2.2.2.2
    rw [wOf_frame (R := R) hfr hdo' (fun h => (hn.2.2.2.1 h).2.2.2.2.2), hrn] at hR
    refine ⟨hfr.trans hfrm (fun a n h => ?_), j0, j3, j1, hR⟩
    simp only [NilFLE, outside_append] at h
    exact ⟨h.2, h.1⟩
  · obtain ⟨hf, hx, hzv, hinv, hwin⟩ := hfast hz
    have P1 := FormatPrefix.prefix_nz impl rt stack fW fP fF fWr z tab data ch s hrip hr0 hr3 hr1 hr7 hz hg hal hstk hhi hacc hout
    refine Fv256.SegCompose.seg_trans P1 (fun S0 hr hq => ?_)
    obtain ⟨hz0, hz3, hz1, hz7, hrs4, hrs5, hr14, hxmm, hdf, hfs, h58, h60, hfr, hrbp, hreg⟩ := hq
    have hrn := rsp0_toNat (s := s) (by omega) hrs4
    have hfpre := fpre_of hc' hf hz0 hz3 hz1 hrs4 hrs5 h58 h60 hfr
    obtain ⟨xdl, xg1, xg2, xg3, xgo, xgd, xH⟩ := fx_of hc' hf hx hrs4 hr14 hfr hreg
    obtain ⟨xH1, xH2, xH3, xH4, xH5⟩ := xH
    have hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ z.toNat := hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hzv0 : S0.mem.readLE z.toNat 32 = zv := by rw [rdW (stack := stack) hfr hzd]; exact hzv
    have hWr' : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
        (FastWP data (Fv256.FormatSpec.fastBytes (S0.mem.readLE z.toNat 32) ((S0.regs 7).toNat % 2 ^ 32))) := by
      rw [hzv0, hz7]; exact hWr
    have hra : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [hrn, show (s.regs 4).toNat - 72 + 72 = (s.regs 4).toNat by omega]
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hxS0 : S0.xmm 15 = 0 := by rw [hxmm]; exact hx0
    have hdfS0 : S0.df = false := by rw [hdf]; exact hdf0
    have hwR' : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt := by
      rw [hrn, show (s.regs 4).toNat - 72 - 8 - stack = (s.regs 4).toNat - 80 - stack by omega]; exact hwin
    have hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47 := by rw [hra]; exact hretv
    have hrt := fast_amd64 impl R2 rt H stack fW fP fF fWr RW RP RF RWr z tab data hI hW hP hF S0 hWr' hcL hcP hc2L hrt32 hr hfpre hwR'
      h4568 xdl hdrt ht1 ht2 ht3 xg1 xg2 xg3 xgo xgd hxS0 hdfS0 xH1 xH2 xH3 xH4 xH5 hret47
    obtain ⟨k, S', hsteps, t, ht, hrip', hq'⟩ := hrt
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rw [retAddrOf_eq, ← hra]
    rcases ht with rfl | rfl
    · refine ⟨k, S', hsteps, hrip', ?_⟩
      obtain ⟨⟨e4, e5, e14, ex, hfrm, hwr⟩, hph, hch⟩ := hq'
      rw [hz7] at hph hch
      refine ⟨abi_of (by omega) hrs4 hrbp hr14 hxmm e4 e5 e14 ex, fun h => absurd h hz, fun _ => Or.inl ?_⟩
      rw [hrn] at hfrm
      refine ⟨hfr.trans hfrm (fun a n h => ?_), hwr, hph, hch⟩
      simp only [outside_append] at h
      exact ⟨h.2, h.1⟩
    · obtain ⟨hfi, hk, hnp⟩ := hq'
      rw [hz7] at hnp
      have hfi' := hfi
      obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hfi'
      have hinv0 : R2.inv b0 [] (S0.regs 14).toNat (view R2.rt [] S0.mem) := by
        rw [hr14, view_frame hfr hreg hstk hwin]; exact hinv
      have hinv1 : R2.inv b0 [] (S'.regs 14).toNat (view R2.rt [] S'.mem) := by rw [i14]; exact hk b0 [] hinv0
      have hfi2 : FInv rt stack z tab data (ch.toNat % 2 ^ 32) S0 S' := by rw [hz7] at hfi; exact hfi
      obtain ⟨k2, S2, hs2, hr2, hq2⟩ := hbig S0 S' hz hfpre hzv0 hnp hrip' hfi2 hinv1
      refine ⟨k + k2, S2, hsteps.trans hs2, hr2, ?_⟩
      obtain ⟨b4, b5, b14, bx, bfr, bP⟩ := hq2
      refine ⟨abi_of (by omega) hrs4 hrbp hr14 hxmm b4 b5 b14 bx, fun h => absurd h hz, fun _ => Or.inr ?_⟩
      rw [hrn] at bfr
      refine ⟨hfr.trans bfr (fun a n h => ?_), hnp, bP⟩
      simp only [outside_append] at h
      exact ⟨h.2, by simp only [outside_append]; exact h.1⟩

end Fv256.Amd64.Format
