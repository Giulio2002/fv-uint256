import Fv256.Arm64.SfdFdPro

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fd_eof (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 fd)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS = 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (s.regs 30) s (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨hl1, hl2, h0, h1, h2, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA, hfin⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hacc : s.mem.accessible (s.sp.toNat - 168) 200 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hg : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 32 < s.sp.toNat := by omega
  have hz0 := hz.1
  have hEOF0 := hEOFo
  simp only [outside_cons, outside_nil, and_true] at hEOF0
  obtain ⟨hEOF1', hEOF2'⟩ := hEOF0
  have hEOF1 : 1793040 + 16 ≤ lo ∨ hi ≤ 1793040 := hEOF1'
  have hEOF2 : 1793040 + 16 ≤ z.toNat ∨ z.toNat + 32 ≤ 1793040 := hEOF2'
  subst hn
  janus_run [h0, h1, h2, hacc, hg, hEOF, hEOF1, hEOF2]
  all_goals (
    have hn0 : (0#64 : BitVec 64).toNat = 0 := rfl
    unfold FdPost
    refine ⟨rfl, ?_, ?_, ?_, ?keep, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    case keep =>
      unfold Keep
      refine ⟨?_, ?_⟩ <;> (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · rw [hn0]; exact fromDec_eof _
    · simp [setReg_apply]
    · simp [setReg_apply]
    · dsimp only
      unfold Janus.Spec.val256
      rw [Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_mod]
    · refine Env.frame hMod.1 hEnv ?_ ?_ ?_ hzR hzP hzS hzg
      · exact ⟨e1, by omega, e4⟩
      · simp [setReg_apply]
      · dsimp only
        repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
          | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    · dsimp only
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega))

end Fv256.Arm64.SfdFd
