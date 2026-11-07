import Fv256.Amd64.SfdTopH

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

theorem ret_of_ctx {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s Sc S1 : State} {RA : Nat} (hctx : FdCtx R R2 T b L lo hi z pS nS s RA Sc) (hRA : RA < 2 ^ 64)
    (hlo : 72 ≤ (s.regs 4).toNat) (h : S1.rip = retAddrOf Sc) : S1.rip = BitVec.ofNat 64 RA := by
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hctx.1.1]; exact bv_sub_c _ 72 (by decide) hlo
  rw [h]; simp only [retAddrOf]
  rw [hs72, hctx.2.2.2.2]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- `SetFromDecimal` (amd64), from the `fromDecimal` summary's contracts and the `runtime.cmpstring` contract -/
theorem sfd_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hif : Ifaceeq (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.cmpstring") 16) :
    SfdSummary extCfg (Fv256.Amd64.SfdProg.program.link impl) sfd R R2 T b L lo hi z pS nS := by
  intro s hpc hpre
  have hpre' := hpre
  have hlo72 : 72 ≤ (s.regs 4).toNat := by have := hpre.2.2.2.2.2.2.1; omega
  refine Fv256.SegCompose.seg_trans (top_front impl R R2 T b L lo hi z pS nS s hpc hpre) ?_
  intro S hpc1 hM
  by_cases hlt : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 78
  · refine Fv256.SegCompose.seg_trans (top_c1 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM hlt) ?_
    intro Sc hpc2 hq
    obtain ⟨hpreFd, hctx⟩ := hq
    refine ReachesRet.call (fd_sum impl R R2 T b L lo ((s.regs 4).toNat - 40) z (Sc.regs 3) (Sc.regs 1) hif hnew hmg hmv hwb1 hwb2)
      hpc2 hpreFd ?_
    intro S1 hpc' hpost
    exact top_fin impl R R2 T b L lo hi z pS nS s hpre' Sc S1 4933361 (Or.inl rfl) hctx
      (ret_of_ctx hctx (by decide) hlo72 hpost.1.1) hpost (Fv256.TopMath.decParse_lt _ _ hlt)
  · by_cases hgt : 78 < nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
    · refine Fv256.SegCompose.seg_trans (top_c2 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM hgt) ?_
      intro S' hpc2 hSt
      exact top_range impl R R2 T b L lo hi z pS nS s hpre' S' (sfd + 0xb8) (Or.inl rfl) hpc2 hSt
        (Fv256.TopMath.decParse_big _ _ hgt)
    · have heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78 := by omega
      refine Fv256.SegCompose.seg_trans (top_c3a impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM heq) ?_
      intro Sc hpc2 hq
      obtain ⟨hpr, hC⟩ := hq
      refine ReachesRet.call hcmp hpc2 hpr ?_
      intro S'' hpc'' hret
      by_cases hlex : lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat
          (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78
      · exact top_c3_gt impl R R2 T b L lo hi z pS nS s hpre' Sc S'' hC hpr hret hlex
      · refine Fv256.SegCompose.seg_trans (top_c3_le impl R R2 T b L lo hi z pS nS s hpre' Sc S'' hC hpr hret hlex) ?_
        intro Sc3 hpc3 hq3
        obtain ⟨hpreFd, hctx⟩ := hq3
        refine ReachesRet.call (fd_sum impl R R2 T b L lo ((s.regs 4).toNat - 40) z (Sc3.regs 3) (Sc3.regs 1) hif hnew hmg hmv hwb1 hwb2)
          hpc3 hpreFd ?_
        intro S1 hpc' hpost
        exact top_fin impl R R2 T b L lo hi z pS nS s hpre' Sc3 S1 4933330 (Or.inr rfl) hctx
          (ret_of_ctx hctx (by decide) hlo72 hpost.1.1) hpost (Fv256.TopMath.decParse_eq _ _ heq hlex)

end Fv256.Amd64.SfdTop

#print axioms Fv256.Amd64.SfdTop.sfd_sum
#print axioms Fv256.Amd64.SfdFd.fd_sum
#print axioms Fv256.Amd64.SfdPw.pw_sum
