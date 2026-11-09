import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanB0
import Fv256.Proofs.Amd64.ScanB1
import Fv256.Proofs.Amd64.ScanB2
import Fv256.Proofs.Amd64.ScanB3

/-!
# `Scan` (amd64), Level B glue: the dispatch on the dynamic type word (nil / string / `[]byte` / other)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanB

set_option maxRecDepth 100000 in
/-- Scan with a `[]byte` source: `bytes_seg1`, the call of `slicebytetostring`, `bytes_tail` -/
theorem scan_bytes (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsci : SciSumm (Extracted.program.link impl) R R2 T)
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s)
    (htw : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65») :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨h0, h3, h1, hlo, hhi, hcase⟩ := hpre
  rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨hdw1, hdw2⟩, hdwo, hrtA, hav, htls, hPreV, hPg⟩ | ⟨-, -, h, -⟩
  · exfalso; rw [h] at htw; exact absurd htw (by decide)
  · exfalso; rw [h] at htw; exact absurd htw (by decide)
  · have hPre := Fv256.Amd64.ScanBSb.PreBS.of cfg hPreV
    exact bytes_seg1 R R2 T b _ impl lo hi dst tw dw s _ hpc hret hdl hPre.env hlo hhi h0 h3 h1 htw hdw1 hdw2 hdwo
      (fun S0 hAt => bytes_call impl R R2 T b L lo hi dst tw dw s S0 hret hdl hsb hsci htw hPreV hav hPg htls hrtA hAt)
  · exfalso; exact h htw

/-- the dispatch of `Scan` on the type word -/
theorem scan_top (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsci : SciSumm (Extracted.program.link impl) R R2 T)
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  by_cases h0 : tw = 0
  · exact scan_nil impl R R2 T b L lo hi dst tw dw s hpc hret hpre h0
  · by_cases h1 : tw.toNat = Extracted.dataAddr.«type:string#f88732b8»
    · exact scan_str impl R R2 T b L lo hi dst tw dw s hpc hret hdl hsci hpre h1
    · by_cases h2 : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65»
      · exact scan_bytes impl R R2 T b L lo hi dst tw dw s hpc hret hdl hsb hsci hpre h2
      · exact scan_other impl R R2 T b L lo hi dst tw dw s hpc hret hdl hnew hpre ⟨h0, h1, h2⟩

end Fv256.Amd64.ScanB
