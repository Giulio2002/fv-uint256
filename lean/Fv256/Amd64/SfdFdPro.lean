import Fv256.Amd64.SfdFdHd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the prologue (stack check, frame, zeroing `z`, the copy of `multipliers`) up to the loop head, for a non-empty string -/
theorem fd_pro (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 fd)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS ≠ 0) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 head) s (FdInv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hacc : s.mem.accessible ((s.regs 4).toNat - 144) 168 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hmo := hMult.2.1
  simp only [outside_cons, outside_nil, and_true] at hmo
  obtain ⟨hmA0, hmB0⟩ := hmo
  have hmA : 5997952 + 40 ≤ lo ∨ hi ≤ 5997952 := hmA0
  have hmB : 5997952 + 40 ≤ z.toNat ∨ z.toNat + 32 ≤ 5997952 := hmB0
  have hmacc : s.mem.accessible 5997952 40 false = true := hMult.1
  have hz0 := hz
  have hnz : ¬ (nS.toNat = 0) := fun h => hn (BitVec.eq_of_toNat_eq h)
  have hs4 : (s.regs 4 - 144#64).toNat = (s.regs 4).toNat - 144 := bv_sub_c _ 144 (by decide) (by omega)
  janus64_run [h0, h1, h3, hnz, hacc, hmA, hmB, hmacc] until [head]
  all_goals (
    refine reach_name ?_
    intro S2 hS2
    have h4 : S2.regs 4 = s.regs 4 - 144#64 := by simp [hS2, setRegF_apply]
    have hs4' : (S2.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [h4]; exact hs4
    have hg2 : S2.regs 14 = s.regs 14 := by simp [hS2, setRegF_apply]
    have hmf : MemFrame s.mem S2.mem [(lo, hi), (z.toNat, z.toNat + 32)] := by
      rw [hS2]; dsimp only
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    refine ReachesRet.done (by rw [hS2]; first | rfl | decide | simp [head, fd]) ?_
    unfold FdInv
    refine ⟨by rw [hS2]; first | rfl | simp [head, fd], by omega, ?r0, ?r3, ?r2, ?r1, ?r6, h4, ?r5, hg2, ?rx, ?rdf, ?rfs, hmf, ?mret, ?mbp, ?mz, ?mp, ?tab, ?val, ?env, ?fb, ?ad⟩
    case r0 => simp [hS2, setRegF_apply, h0]
    case r3 => simp [hS2, setRegF_apply, h3]
    case r2 => simp [hS2, setRegF_apply]
    case r1 => simp [hS2, setRegF_apply, h1]
    case r6 => intro _; simp [hS2, setRegF_apply, h1]
    case r5 => simp [hS2, setRegF_apply]
    case rx => rw [hS2]; simpa [setXmmF] using hx15
    case rdf => simp [hS2, hdf]
    case rfs => rw [hS2]
    case mret =>
      rw [hS2]; dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    case mbp =>
      rw [hS2]; dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case mz =>
      rw [hS2]; dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case mp =>
      rw [hS2]; dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case tab =>
      intro k hk
      rw [hS2]; dsimp only
      exact tab_word _ s.mem (s.regs 4).toNat 5997952 (by omega) k hk
    case val =>
      rw [hS2]; dsimp only
      unfold Janus.Spec.val256
      rw [accV_zero]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact zero32 _ z.toNat
    case env =>
      exact Env.frame hMod.1 hEnv (by rw [hs4']; refine ⟨by omega, by omega, by omega⟩) hg2 hmf hzR hzP hzS hzg
    case fb => rfl
    case ad => intro k hk1 hk2; omega)

end Fv256.Amd64.SfdFd
