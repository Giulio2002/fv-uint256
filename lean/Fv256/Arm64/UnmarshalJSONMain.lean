import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Arm64.SfdTopD
import Fv256.Arm64.SfdWitReg
import Fv256.Arm64.SfdLink
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.FromHexLib
import Fv256.Arm64.UnmarshalJSON
import Fv256.Arm64.UnmarshalJSONWitC

/-!
# `(*uint256.Int).UnmarshalText(input []byte) error` (arm64): the Extracted-level theorem

The proof transfers `SfdTop.sfd_sum` (SetFromDecimal, library program `SfdProg`) and `FromHexLib.fromHex_sum` (library program
`FromHexProg`) to `Extracted.program`; the runtime contracts are hypotheses about the runtime's own code `Extracted.program.ofImpl impl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalHex Fv256.Arm64.UnmarshalPost Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalJPost Fv256.Arm64.UnmarshalSpecJ

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.UnmarshalJSONMain

theorem cfg_eq : Fv256.Arm64.UnmarshalJSON.cfg = Fv256.Arm64.SfdTop.cfg := by
  unfold Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.SfdTop.cfg SfdCfg.mk; congr 1 <;> decide

set_option maxRecDepth 200000 in
theorem hsub : ∀ seg ∈ Fv256.Arm64.SfdProg.program.segments, seg ∈ Extracted.program.segments := by decide

set_option maxRecDepth 200000 in
theorem hst : ∀ st ∈ Fv256.Arm64.SfdProg.program.stubs, ∃ st' ∈ Extracted.program.stubs, st'.addr = st.addr := by decide

theorem hex : Fv256.Arm64.SfdProg.program.exitAddr = Extracted.program.exitAddr := rfl

set_option maxRecDepth 200000 in
theorem hsubH : ∀ seg ∈ Fv256.Arm64.FromHexProg.program.segments, seg ∈ Extracted.program.segments := by decide

set_option maxRecDepth 200000 in
theorem hstH : ∀ st ∈ Fv256.Arm64.FromHexProg.program.stubs, ∃ st' ∈ Extracted.program.stubs, st'.addr = st.addr := by decide

theorem hexH : Fv256.Arm64.FromHexProg.program.exitAddr = Extracted.program.exitAddr := rfl

theorem caddr (n : String) (h : n = "runtime.cmpstring" ∨ n = "runtime.ifaceeq" ∨ n = "runtime.mallocgc" ∨ n = "runtime.memmove" ∨
    n = "runtime.newobject" ∨ n = "runtime.gcWriteBarrier1" ∨ n = "runtime.gcWriteBarrier2") :
    Fv256.Arm64.SfdProg.program.contractAddr n = Extracted.program.contractAddr n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sfdEntry_eq : Fv256.Arm64.UnmarshalJSON.sfdEntry = 0xb89b0 := by decide
theorem fhEntry_eq : Fv256.Arm64.UnmarshalJSON.fhEntry = Fv256.Arm64.FromHexLib.fh := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16)
    (hsb : RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R2 T b L lo hi
          z pI nI s ∧ HexEnv R lo hi z s)
      (fun s s' => JPost Fv256.Arm64.UnmarshalJSON.cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  have hc1 := Fv256.Arm64.SfdLink.codeIn_ofImpl_sub Fv256.Arm64.SfdProg.program Extracted.program impl hst hex hsub hI
  have hc2 := Fv256.Arm64.SfdLink.codeIn_link_sub Fv256.Arm64.SfdProg.program Extracted.program impl hsub hst hex hI
  have hc3 := Fv256.Arm64.SfdLink.codeIn_link_sub Fv256.Arm64.FromHexProg.program Extracted.program impl hsubH hstH hexH hI
  have hc4 := Fv256.Arm64.SfdLink.codeIn_ofImpl_sub Extracted.program Extracted.program impl
    (fun st h => ⟨st, h, rfl⟩) rfl (fun seg h => h) hI
  have a1 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.ifaceeq" = Extracted.program.contractAddr "runtime.ifaceeq" :=
    caddr _ (by simp)
  have a2 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.newobject" = Extracted.program.contractAddr "runtime.newobject" :=
    caddr _ (by simp)
  have a3 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.mallocgc" = Extracted.program.contractAddr "runtime.mallocgc" :=
    caddr _ (by simp)
  have a4 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.memmove" = Extracted.program.contractAddr "runtime.memmove" :=
    caddr _ (by simp)
  have a5 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1" = Extracted.program.contractAddr "runtime.gcWriteBarrier1" :=
    caddr _ (by simp)
  have a6 : Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2" = Extracted.program.contractAddr "runtime.gcWriteBarrier2" :=
    caddr _ (by simp)
  have hif' : Contracts.Iface.Ifaceeq (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.ifaceeq") R2 := by
    rw [a1]; exact Summary.of_codeIn hc1 hif
  have hnew' : NewobjectLiveContract (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.newobject") 4096 R := by
    rw [a2]; exact NewobjectLiveContract.of_codeIn hc1 hnew
  have hmg' : MallocgcLiveContract (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.mallocgc") 4096 R := by
    rw [a3]; exact MallocgcLiveContract.of_codeIn hc1 hmg
  have hmv' : MemmoveLive (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.memmove") 4096 R := by
    rw [a4]; exact MemmoveLive.of_codeIn hc1 hmv
  have hwb1' : WbLiveContract (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 := by
    rw [a5]; exact WbLiveContract.of_codeIn hc1 hwb1
  have hwb2' : WbLiveContract (Fv256.Arm64.SfdProg.program.link impl)
      (Fv256.Arm64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 := by
    rw [a6]; exact WbLiveContract.of_codeIn hc1 hwb2
  have hcmp' : Contracts.Cmpstring.CmpstringContract (Fv256.Arm64.SfdProg.program.link impl) 0x11cc0 16 := by
    have e : (0x11cc0 : Nat) = Extracted.program.contractAddr "runtime.cmpstring" := by decide
    rw [e]; exact Summary.of_codeIn hc1 hcmp
  have hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary Fv256.Arm64.UnmarshalJSON.cfg (Extracted.program.link impl) Fv256.Arm64.UnmarshalJSON.sfdEntry R R2 T b' L' lo' hi' z pS' nS' := by
    intro b' L' lo' hi' z' pS' nS'
    have hpw : ∀ (lo'' hi'' : Nat) (p len : BitVec 64), Fv256.Arm64.SfdPw.PwSum impl R R2 T b' L' lo'' hi'' p len :=
      fun lo'' hi'' p len => Fv256.Arm64.SfdPw.pw_sum impl R R2 T b' L' lo'' hi'' p len hif' hnew' hmg' hmv' hwb1' hwb2'
    have hS := Summary.of_codeIn hc2 (Fv256.Arm64.SfdTop.sfd_sum impl R R2 T b' L' lo' hi' z' pS' nS' hpw hcmp')
    rw [cfg_eq, sfdEntry_eq]
    exact hS
  have hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) Fv256.Arm64.UnmarshalJSON.fhEntry
      (FromHexPre z hp len) (FromHexPost z hp len) := by
    intro z' hp len
    rw [fhEntry_eq]
    exact Summary.of_codeIn hc3 (Fv256.Arm64.FromHexLib.fromHex_sum impl z' hp len)
  have hsb' : RtLiveContract (Extracted.program.link impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive :=
    RtLiveContract.of_codeIn hc4 hsb
  exact Fv256.Arm64.UnmarshalJSON.correctness impl R R2 T b L lo hi z pI nI cI hsb' hhex hsfd

namespace Witness
open Fv256.Arm64.UnmarshalJSONWit

/-- Non-vacuity: a concrete runtime (stub code at the contract addresses: allocation, copy, write barriers, interface equality,
string comparison and the live `slicebytetostring` copying a 48-digit input into a fresh block; toy allocator `R`, interface model
`R0`), a stack window and a call `UnmarshalJSON(z, "777…7")` satisfy EVERY hypothesis of `correctness` (the `ImplApart` premise,
the eight runtime contracts, the call setup) and its precondition (`PreU`, `HexEnv`). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 Fv256.Arm64.UnmarshalJSON.sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive Fv256.Arm64.UnmarshalJSON.sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ JPost Fv256.Arm64.UnmarshalJSON.cfg R R2 lo hi z pI.toNat nI.toNat s s' := by
  refine ⟨implA, R, R0, TD, bW, ([]), loW, hiW, zV, pV, nV, nV, retW, s0, implOK, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7, ?h8, ?h9, hret, setup, pre0, hexEnv0, ?hc1, ?hc2, ?hc3, ?hc4, ?hc5, ?hc6, ?hc7, ?hc8,
    correctness implA R R0 TD bW ([]) loW hiW zV pV nV nV implOK ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 ?h9 retW hret s0 setup ⟨hp10, hp11⟩⟩
  case h2 => exact (by rw [addr_if]; exact model_if)
  case h3 => exact (by rw [addr_new]; exact model_new)
  case h4 => exact (by rw [addr_mg]; exact model_mg)
  case h5 => exact (by rw [addr_mv]; exact model_mv)
  case h6 => exact (by rw [addr_w1]; exact model_wb1)
  case h7 => exact (by rw [addr_w2]; exact model_wb2)
  case h8 => exact (by rw [addr_cm]; exact hcmp)
  case h9 => exact (by rw [show Fv256.Arm64.UnmarshalJSON.sbAddr = sbA by decide]; exact model_sb)
  case hc1 => exact (⟨csNew, rfl, csNew_pre⟩)
  case hc2 => exact (⟨csMg, rfl, csMg_pre⟩)
  case hc3 => exact (⟨csMv, rfl, csMv_pre⟩)
  case hc4 => exact (⟨csW1, rfl, csW1_pre⟩)
  case hc5 => exact (⟨csW2, rfl, csW2_pre⟩)
  case hc6 => exact (⟨csCm, rfl, csCm_pre⟩)
  case hc7 => exact (⟨csIf, rfl, csIf_pre⟩)
  case hc8 => exact (⟨csSb, rfl, csSb_pre⟩)

/-- Non-vacuity on the unquoted path: the same runtime and contracts, the input is an unquoted 48-digit string. -/
theorem unquoted : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreJ Fv256.Arm64.UnmarshalJSON.cfg Fv256.Arm64.UnmarshalJSON.sbAddr Fv256.Arm64.UnmarshalJSON.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s ∧ ¬ Quoted s.mem pI.toNat nI.toNat ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 Fv256.Arm64.UnmarshalJSON.sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec Fv256.Arm64.UnmarshalJSON.stAddr) slicebytetostringLive Fv256.Arm64.UnmarshalJSON.sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ JPost Fv256.Arm64.UnmarshalJSON.cfg R R2 lo hi z pI.toNat nI.toNat s s' := by
  refine ⟨implA, R, R0, TD, bW, ([]), loW, hiW, zV, pHV, nU, nU, retW, s1, implOK, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7, ?h8, ?h9, hret, setup1, pre1, hexEnv0, unq1, ?hc1, ?hc2, ?hc3, ?hc4, ?hc5, ?hc6, ?hc7, ?hc8,
    correctness implA R R0 TD bW ([]) loW hiW zV pHV nU nU implOK ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 ?h9 retW hret s1 setup1 ⟨hp10, hp11⟩⟩
  case h2 => exact (by rw [addr_if]; exact model_if)
  case h3 => exact (by rw [addr_new]; exact model_new)
  case h4 => exact (by rw [addr_mg]; exact model_mg)
  case h5 => exact (by rw [addr_mv]; exact model_mv)
  case h6 => exact (by rw [addr_w1]; exact model_wb1)
  case h7 => exact (by rw [addr_w2]; exact model_wb2)
  case h8 => exact (by rw [addr_cm]; exact hcmp)
  case h9 => exact (by rw [show Fv256.Arm64.UnmarshalJSON.sbAddr = sbA by decide]; exact model_sb)
  case hc1 => exact (⟨csNew, rfl, csNew_pre⟩)
  case hc2 => exact (⟨csMg, rfl, csMg_pre⟩)
  case hc3 => exact (⟨csMv, rfl, csMv_pre⟩)
  case hc4 => exact (⟨csW1, rfl, csW1_pre⟩)
  case hc5 => exact (⟨csW2, rfl, csW2_pre⟩)
  case hc6 => exact (⟨csCm, rfl, csCm_pre⟩)
  case hc7 => exact (⟨csIf, rfl, csIf_pre⟩)
  case hc8 => exact (⟨csSb, rfl, csSb_pre⟩)

end Witness

end Fv256.Arm64.UnmarshalJSONMain
