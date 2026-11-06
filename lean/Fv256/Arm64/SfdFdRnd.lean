import Fv256.Arm64.SfdFdPro

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

abbrev pw : Nat := Fv256.Arm64.SfdPw.pw

theorem ChunkOK.mono_win {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64}
    {lo hi lo' hi' : Nat} {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h : ChunkOK R R2 L b sp sl lo hi m) (hf : MemFrame m m' ws) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    ChunkOK R R2 L b sp sl lo' hi' m' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  exact ⟨c1, c2, c3, by rw [hf.accessible]; exact c4, c5, by omega, c7, c8⟩

theorem bv_chunk_p (pS nS : BitVec 64) (i : Nat) (hn : nS.toNat ≤ 78) (hi : 19 * i + 19 ≤ nS.toNat) (hp : pS.toNat + nS.toNat ≤ 2 ^ 48) :
    (pS + (nS - BitVec.ofNat 64 (19 * i + 19))) = BitVec.ofNat 64 (pS.toNat + (nS.toNat - 19 * i - 19)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := nS.isLt; have := pS.isLt
  simp only [Nat.reducePow] at *
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- head of a round (big chunk) up to the call to `strconv.ParseUint` -/
theorem fd_to_pw (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hpw : ∀ (lo' hi' : Nat) (p len : BitVec 64), PwSum impl R R2 T b L lo' hi' p len)
    (hpre : FdPre R R2 T b L lo hi z pS nS s)
    (S : State) (i : Nat) (hI : FdInv R R2 T b L lo hi z pS nS s i S) (hi5 : i < 5) (hrem : 19 * i < nS.toNat)
    (hbig : 19 < nS.toNat - 19 * i) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 pw) S
      (fun S1 => PwPre R R2 T b L (s.sp.toNat - 4440) (s.sp.toNat - 112) (pS + (nS - BitVec.ofNat 64 (19 * i + 19))) 19#64 S1) := by
  obtain ⟨hl1, hl2, h0, h1, h2, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA, hfin⟩ := hpre
  obtain ⟨hpc, hi5', r0, r1, r3, r2, r4, rsp, r29, r28, r18, r30, hfr, m1, m2, m3, m4, mtab, mval, hEnvS, hfb, hall⟩ := hI
  have hS2 : (S.regs 2).toNat = nS.toNat - 19 * i := by
    rw [r2]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
  have hS4 : (S.regs 4).toNat = nS.toNat - 19 * i := by
    rw [r4 hrem]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
  have hS3 : (S.regs 3).toNat = i := by rw [r3]; simp only [BitVec.toNat_ofNat]; omega
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hEnv' := hEnvS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hacc : S.mem.accessible (S.sp.toNat - 8) 190 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  janus_run [hacc, hS2, hS3, hS4, hspS, r0, r1] until [pw]
  all_goals (
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [pw]) ?_
    unfold PwPre
    have hn19 : (19#64 : BitVec 64).toNat = 19 := rfl
    have hspn : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hbp := bv_chunk_p pS nS i hn78 (by omega) hpB
    refine ⟨?l1, ?l2, ?r0, ?r1, ?r2, ?r3, ?len1, ?len2, hMod, ?env, ?lo, ?hi, ?chunk⟩
    case l1 => simp [setReg_apply]
    case l2 => simp [setReg_apply]
    case r0 => simp [setReg_apply]
    case r1 => simp [setReg_apply]
    case r2 => simp [setReg_apply]
    case r3 => simp [setReg_apply]
    case len1 => rw [hn19]; omega
    case len2 => rw [hn19]; omega
    case lo => simp only [hspn]; omega
    case hi => simp only [hspn]; omega
    case chunk =>
      have hbl : (19#64 : BitVec 64) = BitVec.ofNat 64 19 := rfl
      rw [hbp, hbl]
      have hc := hCA (pS.toNat + (nS.toNat - 19 * i - 19)) 19 (by omega) (by omega) (by omega) (by omega)
      refine ChunkOK.mono_win (ws := [(lo, hi), (z.toNat, z.toNat + 32)]) hc ?_ (by omega) (by omega)
      repeat' first
        | exact hfr
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    case env =>
      refine Env.shrink (lo := lo) (hi := hi) (Env.frame0 hMod.1 hEnvS ?_ ?_ ?_ (by omega)) (by omega) (by omega) ?_ ?_
      · show lo ≤ (s.sp - 160#64).toNat ∧ (s.sp - 160#64).toNat + 8 ≤ hi ∧ (s.sp - 160#64).toNat % 16 = 0
        rw [hspn]; refine ⟨by omega, by omega, by omega⟩
      · simp [setReg_apply]
      · repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
      · show s.sp.toNat - 4440 ≤ (s.sp - 160#64).toNat
        rw [hspn]; omega
      · show (s.sp - 160#64).toNat + 8 ≤ s.sp.toNat - 112
        rw [hspn]; omega
    done)

end Fv256.Arm64.SfdFd
