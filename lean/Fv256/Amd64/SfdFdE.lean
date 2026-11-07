import Fv256.Amd64.SfdFdD

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- one round, from the loop head to the next loop head (continuing with `ihn`) -/
theorem fd_round (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
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
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (ihn : ∀ S', FdInv R R2 T b L lo hi z pS nS s (i + 1) S' →
      ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S' (FdPost R R2 T b L lo hi z pS nS s)) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S (FdPost R R2 T b L lo hi z pS nS s) := by
  have hpreC := hpre
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv0, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  have hEnv0' := hEnv0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv0'
  have hcont : ∀ (S2 : State) (d : Nat), MidInv R R2 T b L lo hi z pS nS s i d S2 →
      ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S2 (FdPost R R2 T b L lo hi z pS nS s) := by
    intro S2 d hM
    by_cases hi0 : i = 0
    · subst hi0
      refine Fv256.SegCompose.seg_trans (fd_mid0 impl R R2 T b L lo hi z pS nS s hn78 hlo hhi hz hzw hzW hzR hzP hzS hzg hMod hfin S2 d hM) ?_
      intro S3 hpc3 hq3
      exact Fv256.SegCompose.seg_trans (fd_incr impl R R2 T b L lo hi z pS nS s 0 S3 hn78 hlo hhi hq3) (fun S4 _ hq4 => ihn S4 hq4)
    · refine Fv256.SegCompose.seg_trans (fd_midK impl R R2 T b L lo hi z pS nS s hn78 hlo hhi e4 (by omega) hz hzw hzW hzR hzP hzS hzg hMod hMult hfin S2 i d hM hi0) ?_
      intro S3 hpc3 hq3
      exact Fv256.SegCompose.seg_trans (fd_incr impl R R2 T b L lo hi z pS nS s i S3 hn78 hlo hhi hq3) (fun S4 _ hq4 => ihn S4 hq4)
  have hclo := chunk_lo_eq nS.toNat i
  by_cases hbig : 19 < nS.toNat - 19 * i
  · refine Fv256.SegCompose.seg_trans (fd_to_pw impl R R2 T b L lo hi z pS nS s hpreC S i hI hi5 hrem hbig) ?_
    intro S1 hpc1 hq1
    obtain ⟨hpreP, hctx⟩ := hq1
    refine ReachesRet.call (pw_sum impl R R2 T b L _ _ _ _ hif hnew hmg hmv hwb1 hwb2) hpc1 hpreP ?_
    intro S' hpc' hpost
    refine fd_post_call impl R R2 T b L lo hi z pS nS s hpreC S i hI hi5 hrem (nS.toNat - 19 * (i + 1)) hclo.symm _ _
      rfl ?_ 4933783 (Or.inl rfl) S1 hctx S' hpost hcont
    have e : nS.toNat - 19 * i - (nS.toNat - 19 * (i + 1)) = 19 := by omega
    rw [e]
  · refine Fv256.SegCompose.seg_trans (fd_to_pw_small impl R R2 T b L lo hi z pS nS s hpreC S i hI hi5 hrem (by omega)) ?_
    intro S1 hpc1 hq1
    obtain ⟨hpreP, hctx⟩ := hq1
    refine ReachesRet.call (pw_sum impl R R2 T b L _ _ _ _ hif hnew hmg hmv hwb1 hwb2) hpc1 hpreP ?_
    intro S' hpc' hpost
    have hc0 : nS.toNat - 19 * (i + 1) = 0 := by omega
    refine fd_post_call impl R R2 T b L lo hi z pS nS s hpreC S i hI hi5 hrem (nS.toNat - 19 * (i + 1)) hclo.symm _ _
      ?_ ?_ 4933806 (Or.inr rfl) S1 hctx S' hpost hcont
    · rw [hc0, Nat.add_zero]; exact bvo pS
    · rw [hc0, Nat.sub_zero]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at this; omega

end Fv256.Amd64.SfdFd
