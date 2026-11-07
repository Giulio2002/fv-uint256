import Extracted
import Fv256.Arm64.SfdLink
import Fv256.Arm64.SfdTopD
import Fv256.Arm64.SfdPw
import Fv256.Arm64.ExpMain
import Fv256.Arm64.MoSa.Top
import Fv256.IbsA64
import Fv256.Arm64.ScanSciBase

/-!
# `Scan` (arm64): the callee summaries, discharged from the library proofs

`hsfd` (`SetFromDecimal`), `hexp` (`Exp`), `hmo` (`MulOverflow`), `hibs` (`IndexByteString`) over `Extracted.program.link impl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSci

namespace Fv256.Arm64.ScanDischarge

/-- a library program is `CodeIn` the extraction linked with a runtime implementation -/
theorem codeIn_prog_link (p E : Program) (impl : List Segment)
    (hsub : ∀ seg ∈ p.segments, seg ∈ E.segments)
    (hstub : ∀ seg ∈ p.segments, ∀ st ∈ E.stubs, st.addr < seg.base ∨ seg.base + 4 * seg.words.length ≤ st.addr)
    (hexit : ∀ seg ∈ p.segments, E.exitAddr < seg.base ∨ seg.base + 4 * seg.words.length ≤ E.exitAddr)
    (hI : ImplApart E impl) : CodeIn p (E.link impl) := by
  refine Fv256.Arm64.CodeIn.codeIn_of_sub p (E.link impl) (fun seg hs => ?_) (fun seg hs => hstub seg hs) (fun seg hs => hexit seg hs)
  have hm : seg ∈ E.segments ++ impl := List.mem_append_left _ (hsub seg hs)
  exact ⟨hm, Fv256.Arm64.SfdLink.disj_of_apart hI hm⟩


theorem cfg_eq : cfg = Fv256.Arm64.SfdTop.cfg := by
  unfold cfg Fv256.Arm64.SfdTop.cfg; congr 1 <;> decide

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
theorem hsfd_of (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T : Nat)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    HSfd impl R R2 T := by
  intro b L lo hi z pS nS
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
  rw [cfg_eq]
  exact hS


set_option maxRecDepth 200000 in
theorem hexp_of (impl : List Segment) (hI : ImplApart Extracted.program impl) : HExp impl := by
  have hc : CodeIn Fv256.Arm64.ExpProg.program (Extracted.program.link impl) :=
    codeIn_prog_link _ _ impl (by decide) (by decide) (by decide) hI
  have hdata : ∀ d ∈ Fv256.Arm64.ExpProg.program.data, ∃ d' ∈ Extracted.program.data, d'.base = d.base ∧ d'.bytes = d.bytes := by
    decide
  have hdl : ∀ m, Extracted.program.DataLoaded m → Fv256.Arm64.ExpProg.program.DataLoaded m := by
    intro m h d hd
    obtain ⟨d', hd', hb, hby⟩ := hdata d hd
    obtain ⟨hreg, hbyt⟩ := h d' hd'
    refine ⟨by simpa [hb, hby] using hreg, fun i hi => ?_⟩
    have := hbyt i (by rw [hby]; exact hi)
    simpa [hb, hby] using this
  intro s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, hl⟩
  exact Summary.of_codeIn hc Fv256.Arm64.ExpMain.exp_summary s hpc ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, hdl _ hl⟩

set_option maxRecDepth 200000 in
theorem hmo_of (impl : List Segment) (hI : ImplApart Extracted.program impl) : HMo impl := by
  have hc : CodeIn Fv256.Arm64.MulOverflowProg.program (Extracted.program.link impl) :=
    codeIn_prog_link _ _ impl (by decide) (by decide) (by decide) hI
  intro z x y
  exact Ensures.toSummaryIn (Fv256.Arm64.MoSa.correctness z x y) (by decide) hc

set_option maxRecDepth 200000 in
theorem hibs_of (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry := by
  have hc : CodeIn Fv256.IbsProg64.program (Extracted.program.link impl) :=
    codeIn_prog_link _ _ impl (by decide) (by decide) (by decide) hI
  intro p n c
  exact Summary.of_codeIn hc (Fv256.IndexByte.ibs_lib_64 p n c)

end Fv256.Arm64.ScanDischarge
