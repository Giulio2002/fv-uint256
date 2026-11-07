import Fv256.Arm64.SfdTopC

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.SfdTop

open Fv256.Arm64.SegCompose in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- `SetFromDecimal` (arm64), from the `strconv.ParseUint` summary and the `runtime.cmpstring` contract -/
theorem sfd_sum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hpw : ∀ (lo' hi' : Nat) (p len : BitVec 64), Fv256.Arm64.SfdPw.PwSum impl R R2 T b L lo' hi' p len)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract (Fv256.Arm64.SfdProg.program.link impl) 0x11cc0 16) :
    SfdSummary cfg (Fv256.Arm64.SfdProg.program.link impl) 0xb89b0 R R2 T b L lo hi z pS nS := by
  intro s hpc hpre
  have hpre' := hpre
  refine seg_trans (top_to_mid impl R R2 T b L lo hi z pS nS s hpc hpre) ?_
  intro S hpc1 hM
  by_cases hlt : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat < 78
  · refine seg_trans (top_c1 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM hlt) ?_
    intro Sc hpc2 hq
    obtain ⟨hpreFd, hctx⟩ := hq
    refine ReachesRet.call (Fv256.Arm64.SfdFd.fd_sum impl R R2 T b L lo (s.sp.toNat - 48) z (Sc.regs 1) (Sc.regs 2) hpw)
      hpc2 hpreFd ?_
    intro S1 hpc' hpost
    exact top_fin impl R R2 T b L lo hi z pS nS s hpre Sc S1 0xb8a9c (Or.inl rfl) hctx (by rw [hpc', hctx.2.1])
      hpost (Fv256.TopMath.decParse_lt _ _ hlt)
  · by_cases hgt : 78 < nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat
    · refine seg_trans (top_c2 impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM hgt) ?_
      intro S' hpc2 hSt
      exact top_range impl R R2 T b L lo hi z pS nS s hpre S' 0xb8a80 (Or.inr rfl) hpc2 hSt
        (Fv256.TopMath.decParse_big _ _ hgt)
    · have heq : nS.toNat - startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat = 78 := by omega
      refine seg_trans (top_c3a impl R R2 T b L lo hi z pS nS s hpre S hpc1 hM heq) ?_
      intro S' hpc2 hq
      obtain ⟨hpr, hC⟩ := hq
      refine ReachesRet.call hcmp hpc2 hpr ?_
      intro S'' hpc'' hret
      by_cases hlex : lexGt (fun j => Fv256.C.bytesAt s.mem pS.toNat
          (startPos (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat + j)) maxDigit 78
      · exact top_c3_gt impl R R2 T b L lo hi z pS nS s hpre S' S'' hC hpr hret hlex
      · refine seg_trans (top_c3_le impl R R2 T b L lo hi z pS nS s hpre S' S'' hC hpr hret hlex) ?_
        intro Sc hpc3 hq3
        obtain ⟨hpreFd, hctx⟩ := hq3
        refine ReachesRet.call (Fv256.Arm64.SfdFd.fd_sum impl R R2 T b L lo (s.sp.toNat - 48) z (Sc.regs 1) (Sc.regs 2) hpw)
          hpc3 hpreFd ?_
        intro S1 hpc' hpost
        exact top_fin impl R R2 T b L lo hi z pS nS s hpre Sc S1 0xb8a74 (Or.inr rfl) hctx (by rw [hpc', hctx.2.1])
          hpost (Fv256.TopMath.decParse_eq _ _ heq hlex)

end Fv256.Arm64.SfdTop
