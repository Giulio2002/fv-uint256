import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.MustFromDecimal
import Fv256.Proofs.Arm64.SfdTopD
import Fv256.Proofs.Arm64.SfdLink
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.MFdWitC

/-!
# `MustFromDecimal` (arm64): the Extracted-level theorem (SetFromDecimal discharged from the library program `SfdProg`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel Janus.Contracts.Panic Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MustFromDecimalMain
open Fv256.Arm64.MustFromDecimal

theorem cfg_eq : Fv256.Arm64.MustFromDecimal.cfg = Fv256.Arm64.SfdTop.cfg := by
  unfold Fv256.Arm64.MustFromDecimal.cfg Fv256.Arm64.SfdTop.cfg; congr 1 <;> decide

set_option maxRecDepth 200000 in
theorem hsub : ∀ seg ∈ Fv256.Arm64.SfdProg.program.segments, seg ∈ Extracted.program.segments := by decide

set_option maxRecDepth 200000 in
theorem hst : ∀ st ∈ Fv256.Arm64.SfdProg.program.stubs, ∃ st' ∈ Extracted.program.stubs, st'.addr = st.addr := by decide

theorem hex : Fv256.Arm64.SfdProg.program.exitAddr = Extracted.program.exitAddr := rfl

theorem caddr (n : String) (h : n = "runtime.cmpstring" ∨ n = "runtime.ifaceeq" ∨ n = "runtime.mallocgc" ∨ n = "runtime.memmove" ∨
    n = "runtime.newobject" ∨ n = "runtime.gcWriteBarrier1" ∨ n = "runtime.gcWriteBarrier2") :
    Fv256.Arm64.SfdProg.program.contractAddr n = Extracted.program.contractAddr n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sfdEntry_eq : Fv256.Arm64.MustFromDecimal.sfdEntry = 0xb89b0 := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
open Fv256.C in
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]))
      (fun s v _ =>
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
        (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
          InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)) := by
  have hc1 := Fv256.Arm64.SfdLink.codeIn_ofImpl_sub Fv256.Arm64.SfdProg.program Extracted.program impl hst hex hsub hI
  have hc2 := Fv256.Arm64.SfdLink.codeIn_link_sub Fv256.Arm64.SfdProg.program Extracted.program impl hsub hst hex hI
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
      SfdSummary Fv256.Arm64.MustFromDecimal.cfg (Extracted.program.link impl) Fv256.Arm64.MustFromDecimal.sfdEntry R R2 T b' L' lo' hi' z pS' nS' := by
    intro b' L' lo' hi' z' pS' nS'
    have hpw : ∀ (lo'' hi'' : Nat) (p len : BitVec 64), Fv256.Arm64.SfdPw.PwSum impl R R2 T b' L' lo'' hi'' p len :=
      fun lo'' hi'' p len => Fv256.Arm64.SfdPw.pw_sum impl R R2 T b' L' lo'' hi'' p len hif' hnew' hmg' hmv' hwb1' hwb2'
    have hS := Summary.of_codeIn hc2 (Fv256.Arm64.SfdTop.sfd_sum impl R R2 T b' L' lo' hi' z' pS' nS' hpw hcmp')
    rw [cfg_eq, sfdEntry_eq]
    exact hS
  have hnew'' : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R := NewobjectLiveContract.of_codeIn hc4 hnew
  exact Fv256.Arm64.MustFromDecimal.correctness_cond P impl R R2 T b L lo hi pS nS hnew'' hsfd

namespace Witness
set_option maxRecDepth 100000 in
/-- non-vacuity: stub runtime contracts, a 48-digit decimal string, a call state with `Pre` (incl. `DataLoaded` of the real data and `PanicInit`) -/
theorem nonvacuous : ∃ (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (pS nS : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pS, nS] s ∧
    (Fv256.Arm64.MFdWit.pinPanicRuntime P ∧ Fv256.Arm64.MustFromDecimal.Pre R R2 T b L lo hi pS nS s) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ (∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])
      | .panicked v s' => (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
        (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
          InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)
      | .goexited _ => False := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, P, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, hret, hsetup, hp9, cs1, cs2, cs3, cs4, cs5, cs6, cs7⟩ := Fv256.Arm64.MFdWit.nonvacuous_core
  exact ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, P, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, hret, hsetup, hp9, cs1, cs2, cs3, cs4, cs5, cs6, cs7,
    correctness P impl R R2 T b L lo hi pS nS h1 h2 h3 h4 h5 h6 h7 h8 ret hret s hsetup (hp9).2⟩

end Witness

end Fv256.Arm64.MustFromDecimalMain
