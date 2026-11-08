import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanB5
import Fv256.Amd64.ScanDisch
import Fv256.Amd64.ScanWitC

/-!
# `(*uint256.Int).Scan(src any) error` (amd64), conditional on the `SetFromDecimal` summary `hsfd` and `IndexByteString` `hibs`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.Scan

theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, tw, dw]
      (fun s => ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s') := by
  exact Fv256.Amd64.ScanB.correctness_cond impl R R2 T b L lo hi dst tw dw hnew hsb (Fv256.Amd64.ScanDisch.disch_ibs impl)
    (Fv256.Amd64.ScanDisch.disch_sfd impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp) (Fv256.Amd64.ScanDisch.disch_exp impl)
    (Fv256.Amd64.ScanDisch.disch_mo impl)


namespace Witness

/-- Non-vacuity (string "123456789012e5": both SfdCalls, the Exp and MulOverflow path): a concrete runtime (stub code at the contract addresses, toy allocator `R`, the interface model at the
binary's own type word, the binary's real read-only data), a stack window and a call `Scan(dst, src)` satisfy EVERY hypothesis of
`correctness` and its whole precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s' := by
  refine ⟨Fv256.Amd64.Scan.Witness.implA, Fv256.Amd64.Scan.Witness.R, Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW, Fv256.Amd64.Scan.Witness.TW, 0x400, [], Fv256.Amd64.Scan.Witness.loW, Fv256.Amd64.Scan.Witness.hiW, Fv256.Amd64.Scan.Witness.zV, Fv256.Amd64.Scan.Witness.twS, Fv256.Amd64.Scan.Witness.dwS, Fv256.Amd64.Scan.Witness.retW, Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS, Fv256.Amd64.Scan.Witness.contracts_ok.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csNew, Fv256.Amd64.Scan.Witness.csNew_rip, Fv256.Amd64.Scan.Witness.csNew_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMg, Fv256.Amd64.Scan.Witness.csMg_rip, Fv256.Amd64.Scan.Witness.csMg_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMv, Fv256.Amd64.Scan.Witness.csMv_rip, Fv256.Amd64.Scan.Witness.csMv_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW1, Fv256.Amd64.Scan.Witness.csW1_rip, Fv256.Amd64.Scan.Witness.csW1_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW2, Fv256.Amd64.Scan.Witness.csW2_rip, Fv256.Amd64.Scan.Witness.csW2_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csCm, Fv256.Amd64.Scan.Witness.csCm_rip, Fv256.Amd64.Scan.Witness.csCm_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csIf, Fv256.Amd64.Scan.Witness.csIf_rip, Fv256.Amd64.Scan.Witness.csIf_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csSb, Fv256.Amd64.Scan.Witness.csSb_rip, Fv256.Amd64.Scan.Witness.csSb_pre⟩, Fv256.Amd64.Scan.Witness.hret, ?w9, Fv256.Amd64.Scan.Witness.preS, Fv256.Amd64.Scan.Witness.dataLoaded0,
    correctness Fv256.Amd64.Scan.Witness.implA Fv256.Amd64.Scan.Witness.R (Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW) Fv256.Amd64.Scan.Witness.TW 0x400 ([]) Fv256.Amd64.Scan.Witness.loW Fv256.Amd64.Scan.Witness.hiW Fv256.Amd64.Scan.Witness.zV Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS Fv256.Amd64.Scan.Witness.contracts_ok.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2 Fv256.Amd64.Scan.Witness.retW Fv256.Amd64.Scan.Witness.hret (Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS) ?w9 ⟨Fv256.Amd64.Scan.Witness.preS, Fv256.Amd64.Scan.Witness.dataLoaded0⟩⟩
  case w9 => exact Fv256.Amd64.Scan.Witness.setup Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS

end Witness

namespace NoE.Witness

/-- Non-vacuity (string without an exponent "1234567890123"): a concrete runtime (stub code at the contract addresses, toy allocator `R`, the interface model at the
binary's own type word, the binary's real read-only data), a stack window and a call `Scan(dst, src)` satisfy EVERY hypothesis of
`correctness` and its whole precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s' := by
  refine ⟨Fv256.Amd64.Scan.Witness.implA, Fv256.Amd64.Scan.Witness.R, Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW, Fv256.Amd64.Scan.Witness.TW, 0x400, [], Fv256.Amd64.Scan.Witness.loW, Fv256.Amd64.Scan.Witness.hiW, Fv256.Amd64.Scan.Witness.zV, Fv256.Amd64.Scan.Witness.twS, Fv256.Amd64.Scan.Witness.dwS2, Fv256.Amd64.Scan.Witness.retW, Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS2, Fv256.Amd64.Scan.Witness.contracts_ok.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csNew, Fv256.Amd64.Scan.Witness.csNew_rip, Fv256.Amd64.Scan.Witness.csNew_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMg, Fv256.Amd64.Scan.Witness.csMg_rip, Fv256.Amd64.Scan.Witness.csMg_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMv, Fv256.Amd64.Scan.Witness.csMv_rip, Fv256.Amd64.Scan.Witness.csMv_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW1, Fv256.Amd64.Scan.Witness.csW1_rip, Fv256.Amd64.Scan.Witness.csW1_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW2, Fv256.Amd64.Scan.Witness.csW2_rip, Fv256.Amd64.Scan.Witness.csW2_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csCm, Fv256.Amd64.Scan.Witness.csCm_rip, Fv256.Amd64.Scan.Witness.csCm_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csIf, Fv256.Amd64.Scan.Witness.csIf_rip, Fv256.Amd64.Scan.Witness.csIf_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csSb, Fv256.Amd64.Scan.Witness.csSb_rip, Fv256.Amd64.Scan.Witness.csSb_pre⟩, Fv256.Amd64.Scan.Witness.hret, ?w9, Fv256.Amd64.Scan.Witness.preN, Fv256.Amd64.Scan.Witness.dataLoaded0,
    correctness Fv256.Amd64.Scan.Witness.implA Fv256.Amd64.Scan.Witness.R (Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW) Fv256.Amd64.Scan.Witness.TW 0x400 ([]) Fv256.Amd64.Scan.Witness.loW Fv256.Amd64.Scan.Witness.hiW Fv256.Amd64.Scan.Witness.zV Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS2 Fv256.Amd64.Scan.Witness.contracts_ok.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2 Fv256.Amd64.Scan.Witness.retW Fv256.Amd64.Scan.Witness.hret (Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS2) ?w9 ⟨Fv256.Amd64.Scan.Witness.preN, Fv256.Amd64.Scan.Witness.dataLoaded0⟩⟩
  case w9 => exact Fv256.Amd64.Scan.Witness.setup Fv256.Amd64.Scan.Witness.twS Fv256.Amd64.Scan.Witness.dwS2

end NoE.Witness

namespace Nil.Witness

/-- Non-vacuity (nil): a concrete runtime (stub code at the contract addresses, toy allocator `R`, the interface model at the
binary's own type word, the binary's real read-only data), a stack window and a call `Scan(dst, src)` satisfy EVERY hypothesis of
`correctness` and its whole precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s' := by
  refine ⟨Fv256.Amd64.Scan.Witness.implA, Fv256.Amd64.Scan.Witness.R, Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW, Fv256.Amd64.Scan.Witness.TW, 0x400, [], Fv256.Amd64.Scan.Witness.loW, Fv256.Amd64.Scan.Witness.hiW, Fv256.Amd64.Scan.Witness.zV, 0#64, 0#64, Fv256.Amd64.Scan.Witness.retW, Fv256.Amd64.Scan.Witness.st 0#64 0#64, Fv256.Amd64.Scan.Witness.contracts_ok.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csNew, Fv256.Amd64.Scan.Witness.csNew_rip, Fv256.Amd64.Scan.Witness.csNew_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMg, Fv256.Amd64.Scan.Witness.csMg_rip, Fv256.Amd64.Scan.Witness.csMg_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMv, Fv256.Amd64.Scan.Witness.csMv_rip, Fv256.Amd64.Scan.Witness.csMv_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW1, Fv256.Amd64.Scan.Witness.csW1_rip, Fv256.Amd64.Scan.Witness.csW1_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW2, Fv256.Amd64.Scan.Witness.csW2_rip, Fv256.Amd64.Scan.Witness.csW2_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csCm, Fv256.Amd64.Scan.Witness.csCm_rip, Fv256.Amd64.Scan.Witness.csCm_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csIf, Fv256.Amd64.Scan.Witness.csIf_rip, Fv256.Amd64.Scan.Witness.csIf_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csSb, Fv256.Amd64.Scan.Witness.csSb_rip, Fv256.Amd64.Scan.Witness.csSb_pre⟩, Fv256.Amd64.Scan.Witness.hret, ?w9, Fv256.Amd64.Scan.Witness.preNil, Fv256.Amd64.Scan.Witness.dataLoaded0,
    correctness Fv256.Amd64.Scan.Witness.implA Fv256.Amd64.Scan.Witness.R (Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW) Fv256.Amd64.Scan.Witness.TW 0x400 ([]) Fv256.Amd64.Scan.Witness.loW Fv256.Amd64.Scan.Witness.hiW Fv256.Amd64.Scan.Witness.zV (0#64) (0#64) Fv256.Amd64.Scan.Witness.contracts_ok.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2 Fv256.Amd64.Scan.Witness.retW Fv256.Amd64.Scan.Witness.hret (Fv256.Amd64.Scan.Witness.st 0#64 0#64) ?w9 ⟨Fv256.Amd64.Scan.Witness.preNil, Fv256.Amd64.Scan.Witness.dataLoaded0⟩⟩
  case w9 => exact Fv256.Amd64.Scan.Witness.setup 0#64 0#64

end Nil.Witness

namespace Byt.Witness

/-- Non-vacuity ([]byte of 48 bytes, 46 digits and e5, through the live slicebytetostring): a concrete runtime (stub code at the contract addresses, toy allocator `R`, the interface model at the
binary's own type word, the binary's real read-only data), a stack window and a call `Scan(dst, src)` satisfy EVERY hypothesis of
`correctness` and its whole precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s' := by
  refine ⟨Fv256.Amd64.Scan.Witness.implA, Fv256.Amd64.Scan.Witness.R, Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW, Fv256.Amd64.Scan.Witness.TW, 0x400, [], Fv256.Amd64.Scan.Witness.loW, Fv256.Amd64.Scan.Witness.hiW, Fv256.Amd64.Scan.Witness.zV, Fv256.Amd64.Scan.Witness.twB, Fv256.Amd64.Scan.Witness.dwB, Fv256.Amd64.Scan.Witness.retW, Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twB Fv256.Amd64.Scan.Witness.dwB, Fv256.Amd64.Scan.Witness.contracts_ok.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csNew, Fv256.Amd64.Scan.Witness.csNew_rip, Fv256.Amd64.Scan.Witness.csNew_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMg, Fv256.Amd64.Scan.Witness.csMg_rip, Fv256.Amd64.Scan.Witness.csMg_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMv, Fv256.Amd64.Scan.Witness.csMv_rip, Fv256.Amd64.Scan.Witness.csMv_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW1, Fv256.Amd64.Scan.Witness.csW1_rip, Fv256.Amd64.Scan.Witness.csW1_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW2, Fv256.Amd64.Scan.Witness.csW2_rip, Fv256.Amd64.Scan.Witness.csW2_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csCm, Fv256.Amd64.Scan.Witness.csCm_rip, Fv256.Amd64.Scan.Witness.csCm_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csIf, Fv256.Amd64.Scan.Witness.csIf_rip, Fv256.Amd64.Scan.Witness.csIf_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csSb, Fv256.Amd64.Scan.Witness.csSb_rip, Fv256.Amd64.Scan.Witness.csSb_pre⟩, Fv256.Amd64.Scan.Witness.hret, ?w9, Fv256.Amd64.Scan.Witness.preByt, Fv256.Amd64.Scan.Witness.dataLoaded0,
    correctness Fv256.Amd64.Scan.Witness.implA Fv256.Amd64.Scan.Witness.R (Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW) Fv256.Amd64.Scan.Witness.TW 0x400 ([]) Fv256.Amd64.Scan.Witness.loW Fv256.Amd64.Scan.Witness.hiW Fv256.Amd64.Scan.Witness.zV Fv256.Amd64.Scan.Witness.twB Fv256.Amd64.Scan.Witness.dwB Fv256.Amd64.Scan.Witness.contracts_ok.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2 Fv256.Amd64.Scan.Witness.retW Fv256.Amd64.Scan.Witness.hret (Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twB Fv256.Amd64.Scan.Witness.dwB) ?w9 ⟨Fv256.Amd64.Scan.Witness.preByt, Fv256.Amd64.Scan.Witness.dataLoaded0⟩⟩
  case w9 => exact Fv256.Amd64.Scan.Witness.setup Fv256.Amd64.Scan.Witness.twB Fv256.Amd64.Scan.Witness.dwB

end Byt.Witness

namespace Other.Witness

/-- Non-vacuity (unsupported type (the type descriptor of uint8)): a concrete runtime (stub code at the contract addresses, toy allocator `R`, the interface model at the
binary's own type word, the binary's real read-only data), a stack window and a call `Scan(dst, src)` satisfy EVERY hypothesis of
`correctness` and its whole precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
      Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧
    Extracted.program.DataLoaded s.mem ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s' := by
  refine ⟨Fv256.Amd64.Scan.Witness.implA, Fv256.Amd64.Scan.Witness.R, Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW, Fv256.Amd64.Scan.Witness.TW, 0x400, [], Fv256.Amd64.Scan.Witness.loW, Fv256.Amd64.Scan.Witness.hiW, Fv256.Amd64.Scan.Witness.zV, Fv256.Amd64.Scan.Witness.twU, 0#64, Fv256.Amd64.Scan.Witness.retW, Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twU 0#64, Fv256.Amd64.Scan.Witness.contracts_ok.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1, Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csNew, Fv256.Amd64.Scan.Witness.csNew_rip, Fv256.Amd64.Scan.Witness.csNew_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMg, Fv256.Amd64.Scan.Witness.csMg_rip, Fv256.Amd64.Scan.Witness.csMg_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csMv, Fv256.Amd64.Scan.Witness.csMv_rip, Fv256.Amd64.Scan.Witness.csMv_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW1, Fv256.Amd64.Scan.Witness.csW1_rip, Fv256.Amd64.Scan.Witness.csW1_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csW2, Fv256.Amd64.Scan.Witness.csW2_rip, Fv256.Amd64.Scan.Witness.csW2_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csCm, Fv256.Amd64.Scan.Witness.csCm_rip, Fv256.Amd64.Scan.Witness.csCm_pre⟩, ⟨Fv256.Amd64.Scan.Witness.csIf, Fv256.Amd64.Scan.Witness.csIf_rip, Fv256.Amd64.Scan.Witness.csIf_pre⟩, ⟨[], 0x400, Fv256.Amd64.Scan.Witness.csSb, Fv256.Amd64.Scan.Witness.csSb_rip, Fv256.Amd64.Scan.Witness.csSb_pre⟩, Fv256.Amd64.Scan.Witness.hret, ?w9, Fv256.Amd64.Scan.Witness.preOther, Fv256.Amd64.Scan.Witness.dataLoaded0,
    correctness Fv256.Amd64.Scan.Witness.implA Fv256.Amd64.Scan.Witness.R (Fv256.Amd64.WitModel.R3 Fv256.Amd64.Scan.Witness.TW) Fv256.Amd64.Scan.Witness.TW 0x400 ([]) Fv256.Amd64.Scan.Witness.loW Fv256.Amd64.Scan.Witness.hiW Fv256.Amd64.Scan.Witness.zV Fv256.Amd64.Scan.Witness.twU (0#64) Fv256.Amd64.Scan.Witness.contracts_ok.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.1 Fv256.Amd64.Scan.Witness.contracts_ok.2.2.2.2.2.2.2 Fv256.Amd64.Scan.Witness.retW Fv256.Amd64.Scan.Witness.hret (Fv256.Amd64.Scan.Witness.st Fv256.Amd64.Scan.Witness.twU 0#64) ?w9 ⟨Fv256.Amd64.Scan.Witness.preOther, Fv256.Amd64.Scan.Witness.dataLoaded0⟩⟩
  case w9 => exact Fv256.Amd64.Scan.Witness.setup Fv256.Amd64.Scan.Witness.twU 0#64

end Other.Witness

end Fv256.Amd64.Scan
