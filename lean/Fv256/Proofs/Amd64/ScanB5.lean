import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanA8
import Fv256.Proofs.Amd64.ScanB4
import Fv256.Proofs.Amd64.SummaryEnsures

/-!
# `Scan` (amd64): `Level A` + `Level B` composed, conditional on the library summaries (`hibs`, `hsfd`, `hexp`, `hmo`)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanB

/-- `RetOK` (the return slot readable) follows from the entry facts, in every case of the type word -/
theorem retOK_of_pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (s : State)
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s)
    (hx : s.xmm 15 = 0) (hdf : s.df = false) (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) : RetOK s := by
  obtain ⟨-, -, -, hlo, hhi, hcase⟩ := hpre
  have key : s.mem.accessible lo (hi - lo) true = true → RetOK s := fun e5 =>
    ⟨Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega), hret, hx, hdf⟩
  rcases hcase with ⟨-, -, -, hwin, -⟩ | ⟨-, -, -, -, -, hTop, -⟩ | ⟨-, -, -, -, -, -, hPreV, -⟩ | ⟨-, -, -, -, -, -, -, hEnv, -⟩
  · exact key hwin
  · exact key hTop.env.2.2.2.2.1
  · exact key (Fv256.Amd64.ScanBSb.PreBS.of cfg hPreV).env.2.2.2.2.1
  · exact key hEnv.2.2.2.2.1

set_option maxRecDepth 100000 in
/-- **`Scan` (amd64)**, conditional on the library summaries of `IndexByteString`, `SetFromDecimal`, `Exp` and `MulOverflow` -/
theorem correctness_cond (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hibs : Fv256.IndexByte.IbsLibA (Extracted.program.link impl) ibsEntry avxAddr)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : Fv256.Amd64.ScanA.ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, Fv256.Amd64.ScanA.MoSumm (Extracted.program.link impl) z x y) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, tw, dw]
      (fun s => ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s') := by
  have hsci : SciSumm (Extracted.program.link impl) R R2 T := by
    intro b L lo hi dst p n s hpc ⟨hp, hd⟩
    exact Fv256.Amd64.ScanA.sci_summary impl R R2 T b L lo hi dst p n s hpc hibs hsfd hexp hmo hp hd
  refine Fv256.Amd64.SummaryEnsures.ensures_of_summary64
    (spre := fun s => ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ RetOK s ∧ Extracted.program.DataLoaded s.mem)
    (Q := fun s s' => ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s')
    ?_ ?_ ?_
  · intro s hpc ⟨hp, hret, hd⟩
    exact scan_top impl R R2 T b L lo hi dst tw dw s hpc hret hd hnew hsb hsci hp
  · intro ret s hret hs hp
    obtain ⟨hpU, hd⟩ := hp
    have h := hs.ret
    have e : ((Extracted.program.link impl).withExit ret).exitAddr = ret := rfl
    rw [e] at h
    have h4 : GoABI.regSP = 4 := rfl
    rw [h4] at h
    have hlt : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := by rw [h]; exact hret.user
    exact ⟨hpU, retOK_of_pre R R2 T b L lo hi dst tw dw s hpU hs.zero hs.df hlt, hd⟩
  · intro ret s s' hret hs hp hq
    exact ⟨⟨hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1⟩, hq⟩

end Fv256.Amd64.ScanB
