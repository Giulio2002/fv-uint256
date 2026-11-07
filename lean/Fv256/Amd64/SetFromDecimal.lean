import Extracted
import Fv256.Amd64.SfdLink
import Fv256.Amd64.SummaryEnsures
import Fv256.Amd64.SfdWitC

/-!
# `(*uint256.Int).SetFromDecimal(s string) error` (amd64): the Extracted-level theorem

The statement is `Fv256.Amd64.SfdTopSpec.TopPre/TopPost` instantiated with the addresses of THIS extraction (`extCfg`: every
field is an `Extracted.dataAddr` / `contractAddr`).  The runtime contracts are hypotheses about the linked program `Extracted.program.link impl`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Janus.Contracts.EqHashModel Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg
  Janus.Contracts.Toy Janus.Contracts.IfaceModel

namespace Fv256.Amd64.SetFromDecimal

set_option maxRecDepth 100000 in
theorem entry_eq : Extracted.entry = Fv256.Amd64.SfdTop.sfd := by decide

set_option maxRecDepth 100000 in
/-- the library program (`Fv256.Amd64.SfdProg`, proved Extracted-free) is part of this extraction -/
theorem hLib : Fv256.LinkEq.LibIn Fv256.Amd64.SfdProg.program Extracted.program :=
  Fv256.Amd64.SfdLink.hLib_of_decide (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hca : Fv256.Amd64.SfdLib.ContractsAgree Extracted.program :=
  Fv256.Amd64.SfdLink.hca_of_decide (by decide)

/-- the call-state facts `RetOK` follow from the ABI call setup and the stack window (so the top-level `Ensures` needs no bound on
the caller's return address beyond `RetAddr`) -/
theorem retok_of {p : Janus.Amd64.Program} {ret entry : Nat} {args : List Janus.Amd64.W64} {s : State} {lo hi : Nat}
    (hret : RetAddr p ret) (hs : CallSetup (p.withExit ret) entry args s) (h1 : lo ≤ (s.regs 4).toNat)
    (h2 : (s.regs 4).toNat + 8 ≤ hi) (h3 : s.mem.accessible lo (hi - lo) true = true) : Fv256.C.RetOK s := by
  have h := hs.ret
  have e : (p.withExit ret).exitAddr = ret := rfl
  rw [e] at h
  refine ⟨Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ h3) h1 (by omega), ?_, hs.zero, hs.df⟩
  have h4 : GoABI.regSP = 4 := rfl
  rw [h4] at h
  rw [h]; have := hret.user; omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (fun s => TopPre0 extCfg R R2 T b L lo hi z pS nS s)
      (fun s s' => TopPost extCfg R R2 T b L lo hi z pS nS s s') := by
  rw [entry_eq]
  exact Fv256.Amd64.SummaryEnsures.ensures_of_summary64
    (Fv256.Amd64.SfdLib.hsfd_of_link hLib hca impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp b L lo hi z pS nS)
    (fun ret s hret hs hp => ⟨retok_of hret hs hp.2.2.2.2.1.1 hp.2.2.2.2.1.2.1 hp.2.2.2.2.1.2.2.2.2.1, hp⟩)
    (fun ret s s' hret hs hp hq => ⟨⟨hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1⟩, hq⟩)

namespace Witness

set_option maxRecDepth 100000 in
/-- The hypotheses of `correctness` hold together: a runtime (`impl`, `R`, `R2`), a budget, a stack window and a call of
`SetFromDecimal(z, "7")` (non-empty input) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pS nS : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    TopPre0 extCfg R R2 T b L lo hi z pS nS s :=
  ⟨implA, R, R0, TD, 0x400, [], loW, hiW, zV, pSV, 1#64, retW, s0,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, hret, setup, pre0.2⟩

end Witness

end Fv256.Amd64.SetFromDecimal
