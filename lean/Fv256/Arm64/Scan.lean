import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.ScanSciSpec
import Fv256.Arm64.ScanSpec
import Fv256.Arm64.ScanSciBase
import Fv256.Arm64.ScanSci
import Fv256.Arm64.ScanNil
import Fv256.Arm64.ScanStr
import Fv256.Arm64.ScanByt
import Fv256.Arm64.ScanOther
import Fv256.Arm64.ScanDischarge
import Fv256.Arm64.SummaryEnsures

/-!
# `(*uint256.Int).Scan(src any) error` (arm64)

The statement is `ScanSpec.ScanPre/ScanPost` instantiated with the addresses of THIS extraction.  The runtime contracts are
hypotheses about the runtime's own code `Extracted.program.ofImpl impl`; the callee summaries (`SetFromDecimal`,
`IndexByteString`, `Exp`, `MulOverflow`) are discharged inside the proof from the library proofs.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci

namespace Fv256.Arm64.Scan

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsb : RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, tw, dw]
      (fun s => ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s') := by
  have hsfd := Fv256.Arm64.ScanDischarge.hsfd_of impl R R2 T hI hif hnew hmg hmv hwb1 hwb2 hcmp
  have hexp := Fv256.Arm64.ScanDischarge.hexp_of impl hI
  have hmo := Fv256.Arm64.ScanDischarge.hmo_of impl hI
  have hibs := Fv256.Arm64.ScanDischarge.hibs_of impl hI
  have hcX : Janus.Contracts.EqHashModel.CodeIn (Extracted.program.ofImpl impl) (Extracted.program.link impl) :=
    Fv256.Arm64.SfdLink.codeIn_ofImpl_sub Extracted.program Extracted.program impl (fun st h => ⟨st, h, rfl⟩) rfl (fun _ h => h) hI
  have hnew' : NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R :=
    NewobjectLiveContract.of_codeIn hcX hnew
  have hsb' : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive :=
    RtLiveContract.of_codeIn hcX hsb
  have hsum : Summary (Extracted.program.link impl) Extracted.entry
      (fun s => (ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ Extracted.program.DataLoaded s.mem) ∧
          (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s') := by
    intro s hpc ⟨⟨hpre, hdl⟩, h30a, h30b⟩
    have hpc' : s.pc = BitVec.ofNat 64 Fv256.Arm64.ScanNil.scanEntry := by
      rw [hpc]; congr 1
    obtain ⟨h0, h1, h2, hlo, hhi, h48, hsal, hg, hcases⟩ := hpre
    rcases hcases with ⟨htw0, hd, hw, hacc⟩ | ⟨htw, hdw, hdwW, htop, hinit, hpage⟩ | ⟨htw, hdw, hdwW, hPB, hPG⟩ |
        ⟨htw0, htwS, htwB, htacc, htwW, hMod, hEnv, hok, hb, hdstR, hdstW, hRW⟩
    · -- nil
      have := Fv256.Arm64.ScanNil.scan_nil impl lo hi dst s hpc' h0 (by rw [h1, htw0]) hlo hhi h48 hg hsal hd hw hacc h30a h30b
      obtain ⟨k, s', hst, hr, hq⟩ := this
      exact ⟨k, s', hst, hr, hq.2.2.2.2, Or.inl ⟨htw0, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩⟩
    · -- string
      have := Fv256.Arm64.ScanStr.scan_str impl R R2 T b L lo hi dst tw dw s hpc' h0 h1 h2 hlo hhi h48 hsal hg htw hdw hdwW htop hinit
        hpage hdl h30a h30b hsfd hexp hmo hibs
      obtain ⟨k, s', hst, hr, hq⟩ := this
      exact ⟨k, s', hst, hr, hq.1, Or.inr (Or.inl ⟨htw, hq.2⟩)⟩
    · -- []byte
      have := Fv256.Arm64.ScanByt.scan_byt impl R R2 T b L lo hi dst tw dw s hpc' h0 h1 h2 hlo hhi h48 hsal hg htw hdw hdwW hPB hPG hdl
        h30a h30b hsb' hsfd hexp hmo hibs
      obtain ⟨k, s', hst, hr, hq⟩ := this
      exact ⟨k, s', hst, hr, hq.1, Or.inr (Or.inr (Or.inl ⟨htw, hq.2⟩))⟩
    · -- unsupported type
      have := Fv256.Arm64.ScanOther.scan_other impl R R2 T b L lo hi dst tw dw s hpc' h0 h1 h2 hlo hhi h48 hsal hg htw0 htwS htwB htacc htwW
        hMod hEnv hok hb hRW hdl h30a h30b hnew'
      obtain ⟨k, s', hst, hr, hq⟩ := this
      refine ⟨k, s', hst, hr, hq.1, Or.inr (Or.inr (Or.inr ⟨htw0, htwS, htwB, hq.2.1, hq.2.2.1, ?_, hq.2.2.2⟩))⟩
      show Janus.Spec.val256 s'.mem dst.toNat = Janus.Spec.val256 s.mem dst.toNat
      unfold Janus.Spec.val256
      exact hq.2.2.2.readLE dst.toNat 32 (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hdstR (Nat.le_refl _) (by omega), by omega⟩)
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ hsum ?_ ?_
  · intro ret hret s hsu ⟨hP, hdl⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := hsu.lr
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨⟨hP, hdl⟩, ?_, ?_⟩
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; omega
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; omega
  · intro ret hret s hsu hP s' hq
    exact ⟨⟨hq.1.1, hq.1.2.2.1, hq.1.2.1, hq.1.2.2.2⟩, hq⟩

end Fv256.Arm64.Scan
