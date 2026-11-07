import Extracted
import Fv256.Amd64.CallSites.Live
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

open Fv256.CallSites

/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `RIP` at the stub's entry and the stub's argument registers. -/
def csNew : State := { s0 with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else s0.regs i }
def csW1 : State := { s0 with rip := BitVec.ofNat 64 w1A }
def csW2 : State := { s0 with rip := BitVec.ofNat 64 w2A }
def csMg : State := { s0 with rip := BitVec.ofNat 64 mgA, regs := fun i => if i = 0 then 1 else if i = 3 then 0 else if i = 1 then 0 else s0.regs i }
def csMv : State := { s0 with rip := BitVec.ofNat 64 mvA, regs := fun i => if i = 0 then BitVec.ofNat 64 zW else if i = 3 then BitVec.ofNat 64 0x301000 else if i = 1 then 1 else s0.regs i }
def csCm : State := { s0 with rip := BitVec.ofNat 64 cmA, regs := fun i => if i = 0 then 0 else if i = 3 then 0 else if i = 1 then 0 else if i = 7 then 0 else s0.regs i }
def csIf : State := { s0 with rip := BitVec.ofNat 64 ifA, regs := fun i => if i = 0 then 0 else s0.regs i }
theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr_new]; rfl
theorem csW1_rip : csW1.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") := by rw [addr_w1]; rfl
theorem csW2_rip : csW2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") := by rw [addr_w2]; rfl
theorem csMg_rip : csMg.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") := by rw [addr_mg]; rfl
theorem csMv_rip : csMv.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") := by rw [addr_mv]; rfl
theorem csCm_rip : csCm.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") := by rw [addr_cm]; rfl
theorem csIf_rip : csIf.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") := by rw [addr_if]; rfl
set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_new]; exact Or.inl (⟨rfl, by decide⟩), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 csMg :=
  ⟨⟨by decide, by decide, Or.inl (by decide)⟩, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩,
    by rw [addr_mg]; exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, 1, by decide, by decide, by decide⟩)))), inv0, by decide, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 csMv :=
  ⟨by decide, by rw [addr_mv]; exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, zW, 0x301000, 1, by decide, by decide, by decide⟩)))), inv0, liveSep_nil _, (by rw [rt_eq]; intro r hr; simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide))⟩, by decide,
    by decide, by decide, by rw [rt_eq]; simp only [calleeStack64, outside_cons, outside_nil]; decide, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide), by simp only [outside_cons, outside_nil]; decide⟩

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 :=
  ⟨by decide, by rw [addr_w1]; exact Or.inr (Or.inl (⟨rfl, by decide⟩)), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 :=
  ⟨by decide, by rw [addr_w2]; exact Or.inr (Or.inr (Or.inl (⟨rfl, by decide⟩))), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre64 16 csCm :=
  ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite R0 csIf :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
    fun h => absurd (by decide) h⟩

set_option maxRecDepth 100000 in
/-- The hypotheses of `correctness` hold together: a runtime (`impl`, `R`, `R2`), a budget, a stack window and a call of
`SetFromDecimal(z, s)` for a 45-digit decimal `s` (three chunks of 19, 19 and 7 digits: the multi-word multiply/accumulate path) satisfying the precondition. -/
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
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    TopPre0 extCfg R R2 T b L lo hi z pS nS s ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ TopPost extCfg R R2 T b L lo hi z pS nS s s' := by
  refine ⟨implA, R, R0, TD, 0x400, [], loW, hiW, zV, pSV, nSV, retW, s0, ?w0, ?w1, ?w2, ?w3, ?w4, ?w5, ?w6, ⟨[], 0x400, csNew, csNew_rip, csNew_pre⟩, ⟨[], 0x400, csMg, csMg_rip, csMg_pre⟩, ⟨[], 0x400, csMv, csMv_rip, csMv_pre⟩, ⟨[], 0x400, csW1, csW1_rip, csW1_pre⟩, ⟨[], 0x400, csW2, csW2_rip, csW2_pre⟩, ⟨csCm, csCm_rip, csCm_pre⟩, ⟨csIf, csIf_rip, csIf_pre⟩, hret, setup, pre0.2,
    correctness implA R R0 TD 0x400 ([]) loW hiW zV pSV nSV ?w0 ?w1 ?w2 ?w3 ?w4 ?w5 ?w6 retW hret s0 setup pre0.2⟩
  case w0 => exact by rw [addr_if]; exact model_if
  case w1 => exact by rw [addr_new]; exact model_new
  case w2 => exact by rw [addr_mg]; exact model_mg
  case w3 => exact by rw [addr_mv]; exact model_mv
  case w4 => exact by rw [addr_w1]; exact model_wb1
  case w5 => exact by rw [addr_w2]; exact model_wb2
  case w6 => exact by rw [addr_cm]; exact hcmp

end Witness

end Fv256.Amd64.SetFromDecimal
