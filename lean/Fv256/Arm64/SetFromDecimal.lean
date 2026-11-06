import Extracted
import Fv256.Arm64.SfdTopD
import Fv256.Arm64.SfdLink
import Fv256.Arm64.SummaryEnsures

/-!
# `(*uint256.Int).SetFromDecimal(s string) error` (arm64): the Extracted-level theorem

The statement is `Fv256.Arm64.SfdTopSpec.TopPre/TopPost` instantiated with the addresses of THIS extraction (`cfgE`: every
field is an `Extracted.dataAddr` / `contractAddr`).  The proof transfers `SfdTop.sfd_sum` (about the library program
`SfdProg.program`) to `Extracted.program`.  The runtime contracts are hypotheses about the runtime's own code
`Extracted.program.ofImpl impl` (`ImplApart Extracted.program impl` is the one premise on `impl`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
  Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SetFromDecimal

/-- the addresses of this extraction -/
def cfgE : SfdCfg where
  ioEOF := Extracted.dataAddr.«io.EOF»
  errBig := Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»
  mulTab := Extracted.dataAddr.«github.com/holiman/uint256.multipliers»
  numErrType := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
  numErrItab := Extracted.dataAddr.«go:itab.*strconv.NumError,error»
  errItab := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
  synConst := Extracted.dataAddr.«.rodata#9967e7a3»
  strconvErrSyntax := Extracted.dataAddr.«strconv.ErrSyntax»
  wbFlag := Extracted.dataAddr.«runtime.writeBarrier»
  fnStr := Extracted.dataAddr.«.rodata#7233b75a»
  maxStr := Extracted.dataAddr.«.rodata#575028b4»
  mallocgc := Extracted.program.contractAddr "runtime.mallocgc"
  memmove := Extracted.program.contractAddr "runtime.memmove"
  newobject := Extracted.program.contractAddr "runtime.newobject"
  wb1 := Extracted.program.contractAddr "runtime.gcWriteBarrier1"
  wb2 := Extracted.program.contractAddr "runtime.gcWriteBarrier2"

theorem cfgE_eq : cfgE = Fv256.Arm64.SfdTop.cfg := by
  unfold cfgE Fv256.Arm64.SfdTop.cfg; congr 1 <;> decide

set_option maxRecDepth 200000 in
theorem hsub : ∀ seg ∈ Fv256.Arm64.SfdProg.program.segments, seg ∈ Extracted.program.segments := by decide

set_option maxRecDepth 200000 in
theorem hst : ∀ st ∈ Fv256.Arm64.SfdProg.program.stubs, ∃ st' ∈ Extracted.program.stubs, st'.addr = st.addr := by decide

theorem hex : Fv256.Arm64.SfdProg.program.exitAddr = Extracted.program.exitAddr := rfl

theorem caddr (n : String) (h : n = "runtime.cmpstring" ∨ n = "runtime.ifaceeq" ∨ n = "runtime.mallocgc" ∨ n = "runtime.memmove" ∨
    n = "runtime.newobject" ∨ n = "runtime.gcWriteBarrier1" ∨ n = "runtime.gcWriteBarrier2") :
    Fv256.Arm64.SfdProg.program.contractAddr n = Extracted.program.contractAddr n := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (fun s => TopPre cfgE R R2 T b L lo hi z pS nS s)
      (fun s s' => TopPost cfgE R R2 T b L lo hi z pS nS s s') := by
  have hc1 := Fv256.Arm64.SfdLink.codeIn_ofImpl_sub Fv256.Arm64.SfdProg.program Extracted.program impl hst hex hsub hI
  have hc2 := Fv256.Arm64.SfdLink.codeIn_link_sub Fv256.Arm64.SfdProg.program Extracted.program impl hsub hst hex hI
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
  have hpw : ∀ (lo' hi' : Nat) (p len : BitVec 64), Fv256.Arm64.SfdPw.PwSum impl R R2 T b L lo' hi' p len :=
    fun lo' hi' p len => Fv256.Arm64.SfdPw.pw_sum impl R R2 T b L lo' hi' p len hif' hnew' hmg' hmv' hwb1' hwb2'
  have hS := Summary.of_codeIn hc2 (Fv256.Arm64.SfdTop.sfd_sum impl R R2 T b L lo hi z pS nS hpw hcmp')
  rw [cfgE_eq]
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ hS ?_ ?_
  · intro ret hret s hsu hP; exact hP
  · intro ret hret s hsu hP s' hq
    exact ⟨⟨hq.1, hq.2.2.1, hq.2.1, hq.2.2.2.1⟩, hq⟩

end Fv256.Arm64.SetFromDecimal
