import Fv256.Arm64.SfdFdE

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

theorem toInt_small (x : BitVec 64) (n : Nat) (h : x.toNat = n) (hn : n < 2 ^ 63) : x.toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, h]; split <;> omega

theorem toInt_nonpos (x : BitVec 64) (a b : Nat) (hb : b < 2 ^ 62) (hab : b ≤ a) (ha : a < 2 ^ 62)
    (h : x.toNat = (2 ^ 64 + b - a) % 2 ^ 64) : x.toInt ≤ 0 := by
  rw [BitVec.toInt_eq_toNat_cond, h]; split <;> omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the loop exit (`i = 5` or nothing remaining): return nil -/
theorem fd_nil (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS.toNat ≠ 0)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hex : i = 5 ∨ nS.toNat ≤ 19 * i) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (s.regs 30) S (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hl1, hl2, h0, h1, h2, hn78, hMod, hEnv0, hlo, hhi, hMult, hEOF, hEOFo, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r1, r3, r2, r4, rsp, r29, r28, r18, hfr, m1, m2', m3, m4, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hEnv' := hEnvS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e4' : s.sp.toNat % 16 = 0 := by omega
  have hacc : S.mem.accessible (S.sp.toNat - 8) 190 false = true :=
    Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
  have hx29 : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    have : S.sp.toNat - 8 = s.sp.toNat - 168 := by omega
    rw [this]; exact m2'
  have hx30 : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by
    have : S.sp.toNat = s.sp.toNat - 160 := hspS
    rw [this]; exact m1
  have hS3 : (S.regs 3).toNat = i := by rw [r3]; simp only [BitVec.toNat_ofNat]; omega
  have hS2n : (S.regs 2).toNat = (2 ^ 64 + nS.toNat - 19 * i) % 2 ^ 64 := by
    rw [r2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; simp only [Nat.reducePow] at *; omega
  have hpc' : S.pc = BitVec.ofNat 64 756716 := hpc
  have hret : BitVec.ofNat 64 (S.mem.readLE (s.sp.toNat - 160) 8) = s.regs 30 := by
    rw [m1]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  have hR3i : (S.regs 3).toInt = (i : Int) := toInt_small _ _ hS3 (by omega)
  have hR2i : nS.toNat ≤ 19 * i → (S.regs 2).toInt ≤ 0 := fun h =>
    toInt_nonpos _ (19 * i) nS.toNat (by omega) h (by omega) hS2n
  by_cases h5 : i = 5
  · subst h5
    janus_run [hpc', hret, hacc, hx29, hx30, hS3, hR3i, r0, r1, hspS, hl1, hl2]
    all_goals (
      have hnone : firstBad (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 5 0 = none := by
        rw [hfb]; exact fb_none_five _ _
      have hfd := fromDec_ok_of_none (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (by omega) hnone
      have hval : accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 5 = decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat := by
        unfold accV
        have e1 : nS.toNat - 19 * 5 = 0 := by omega
        have e2 : min nS.toNat (19 * 5) = nS.toNat := by omega
        rw [e1, e2]
      unfold FdPost
      refine ⟨rfl, ?_, ?_, ?_, Or.inr (Or.inl ⟨_, hfd, ?_, ?_, ?_, ?_, ?_⟩)⟩
      · simp [setReg_apply]; rw [m2']; exact (bvo _).symm
      · simp [setReg_apply, r28]
      · simp [setReg_apply, r18]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · dsimp only; rw [mval, hval]
      · refine Env.frame0 hMod.1 hEnvS ⟨by omega, by omega, e4'⟩ (by simp [setReg_apply, r28]) (MemFrame.refl _ _) (by omega)
      · exact hfr)
  · have hle : nS.toNat ≤ 19 * i := by omega
    have hR2 := hR2i hle
    have hR2' : (nS - BitVec.ofNat 64 (19 * i)).toInt ≤ 0 := by rw [← r2]; exact hR2
    janus_run [hpc', hret, hacc, hx29, hx30, hS3, hR3i, hR2, hR2', r0, r1, r2, hspS, hl1, hl2]
    all_goals (
      have hnone : firstBad (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 5 0 = none := by
        rw [hfb]; exact fb_none_of_le _ _ _ (by omega) hle
      have hfd := fromDec_ok_of_none (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (by omega) hnone
      have hval : accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat i = decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat := by
        unfold accV
        have e1 : nS.toNat - 19 * i = 0 := by omega
        have e2 : min nS.toNat (19 * i) = nS.toNat := by omega
        rw [e1, e2]
      unfold FdPost
      refine ⟨rfl, ?_, ?_, ?_, Or.inr (Or.inl ⟨_, hfd, ?_, ?_, ?_, ?_, ?_⟩)⟩
      · simp [setReg_apply]; rw [m2']; exact (bvo _).symm
      · simp [setReg_apply, r28]
      · simp [setReg_apply, r18]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · dsimp only; rw [mval, hval]
      · refine Env.frame0 hMod.1 hEnvS ⟨by omega, by omega, e4'⟩ (by simp [setReg_apply, r28]) (MemFrame.refl _ _) (by omega)
      · exact hfr)

end Fv256.Arm64.SfdFd
