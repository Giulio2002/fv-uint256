import Fv256.Amd64.SfdFdE
import Fv256.Amd64.SfdFdPro
import Fv256.Amd64.SfdFdEof

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the loop exit (`i = 5` or nothing remaining): return nil -/
theorem fd_nil (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS.toNat ≠ 0)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hex : i = 5 ∨ nS.toNat ≤ 19 * i) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) S (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv0, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hEnv' := hEnvS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hacc : S.mem.accessible ((S.regs 4).toNat - 8) 160 false = true :=
    Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
  have hbp : S.mem.readLE ((S.regs 4).toNat + 136) 8 = (s.regs 5).toNat := by
    have : (S.regs 4).toNat + 136 = (s.regs 4).toNat - 8 := by omega
    rw [this]; exact mbp
  have hret : S.mem.readLE ((S.regs 4).toNat + 144) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    have : (S.regs 4).toNat + 144 = (s.regs 4).toNat := by omega
    rw [this]; exact mret
  have hS2 : (S.regs 2).toNat = i := by rw [r2]; simp only [BitVec.toNat_ofNat]; omega
  have hRi : (S.regs 2).toInt = (i : Int) := by rw [BitVec.toInt_eq_toNat_cond, hS2]; split <;> omega
  have hsub : (nS - BitVec.ofNat 64 (19 * i)).toNat = (2 ^ 64 + nS.toNat - 19 * i) % 2 ^ 64 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs8 : (s.regs 4 + 8#64).toNat = (s.regs 4).toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (s.regs 4).isLt; simp only [Nat.reducePow] at *; omega
  have hclose : ∀ S2 : State, S2.rip = retAddrOf s → S2.regs 0 = 0 → S2.regs 3 = 0 → S2.regs 4 = s.regs 4 + 8#64 →
      S2.regs 5 = s.regs 5 → S2.regs 14 = s.regs 14 → S2.xmm 15 = s.xmm 15 → S2.df = s.df → S2.fsBase = s.fsBase →
      S2.mem = S.mem → FdPost R R2 T b L lo hi z pS nS s S2 := by
    intro S2 hrip h0' h3' h4' h5' h14' hx' hdf' hfs' hm
    have hnone : firstBad (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 5 0 = none := by
      by_cases h5 : i = 5
      · subst h5; rw [hfb]; exact fb_none_five _ _
      · rw [hfb]; exact fb_none_of_le _ _ _ (by omega) (by omega)
    have hfd := fromDec_ok_of_none (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (by omega) hnone
    have hval : accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i = decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat := by
      unfold accV
      have e1 : nS.toNat - 19 * i = 0 := by omega
      have e2 : min nS.toNat (19 * i) = nS.toNat := by omega
      rw [e1, e2]
    unfold FdPost Fv256.C.Kept
    refine ⟨⟨hrip, h4', h5', h14', hx', hdf', hfs'⟩, Or.inr (Or.inl ⟨_, hfd, h0', h3', ?_, ?_, ?_⟩)⟩
    · rw [hm, mval, hval]
    · refine Env.frame0 hMod.1 hEnvS ?_ (by rw [h14', r14]) (by rw [hm]; exact MemFrame.refl _ _) (by omega)
      rw [h4', hs8]; refine ⟨by omega, by omega, by omega⟩
    · rw [hm]; exact hfr
  by_cases h5 : i = 5
  · subst h5
    janus64_run [hacc, hS4, hbp, hret, hS2, hRi, r0, r1, r3, r2]
    all_goals (
      refine hclose _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | rfl | simp [setRegF_apply, r14, rx15, hx15, rdf, hdf, rfs])
  · have hle : nS.toNat ≤ 19 * i := by omega
    by_cases heq : nS.toNat = 19 * i
    · have hzf : (18446744073709551616 - 19 * i + nS.toNat) % 18446744073709551616 = 0 := by omega
      janus64_run [hacc, hS4, hbp, hret, hS2, hRi, hzf, r0, r1, r3, r2]
      all_goals (
        refine hclose _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | simp [setRegF_apply, r14, rx15, hx15, rdf, hdf, rfs])
    · have hmsb : (nS - BitVec.ofNat 64 (19 * i)).msb = true := by
        rw [BitVec.msb_eq_decide, hsub]; simp; omega
      have hzf : (18446744073709551616 - 19 * i + nS.toNat) % 18446744073709551616 ≠ 0 := by omega
      janus64_run [hacc, hS4, hbp, hret, hS2, hRi, hzf, hmsb, r0, r1, r3, r2]
      all_goals (
        refine hclose _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | simp [setRegF_apply, r14, rx15, hx15, rdf, hdf, rfs])

end Fv256.Amd64.SfdFd
