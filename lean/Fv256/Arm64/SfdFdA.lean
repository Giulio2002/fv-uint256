import Fv256.Arm64.SfdFdInc

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

/-- the merge point after `ParseUint` returned the digits value `d` of round `i` (no error) -/
def MidInv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i d : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 mid ∧ i < 5 ∧ 19 * i < nS.toNat ∧ d < 2 ^ 64 ∧
  S.regs 0 = BitVec.ofNat 64 d ∧ S.regs 1 = 0 ∧ S.regs 4 = nS - BitVec.ofNat 64 (19 * i) ∧
  S.flags = (addSub (nS - BitVec.ofNat 64 (19 * i)) (19#64) true).snd ∧
  S.sp = s0.sp - 160#64 ∧ S.regs 29 = s0.sp - 168#64 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 18 = s0.regs 18 ∧
  S.mem.readLE (s0.sp.toNat - 104) 8 = i ∧ S.mem.readLE (s0.sp.toNat - 96) 8 = nS.toNat - 19 * i ∧
  S.mem.readLE (s0.sp.toNat - 56) 8 = s0.mem.readLE (mulTab + 8 * i) 8 ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.sp.toNat - 160) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 168) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = z.toNat ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE (s0.sp.toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat i ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - i) i ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i) ∧
  d = decSum (Fv256.C.bytesAt s0.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1) ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * i) nS.toNat

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- round 0: `z := d` -/
theorem fd_mid0 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4440 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hzw : s.mem.accessible z.toNat 32 true = true) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hzR : Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L)
    (hzP : Outside z.toNat 32 R2.priv) (hzS : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)])
    (hzg : (s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)
    (hMod : Mod R R2 T L) (hfin : allDec (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (Fv256.C.bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)
    (S : State) (d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s 0 d S) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 m2) S (M2Inv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨hpc, hi5, hrem, hd64, r0, r1, r4, hfl, rsp, r29, r28, r18, mi, mlen, mW, hfr, m1, m2', m3, m4, mtab, mval, hEnv, hfb, hdig, hd, hall⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (S.sp.toNat - 8) 190 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hiS : S.mem.readLE (S.sp.toNat + 56) 8 = 0 := by
    have : S.sp.toNat + 56 = s.sp.toNat - 104 := by omega
    rw [this]; exact mi
  have hzS' : S.mem.readLE (S.sp.toNat + 168) 8 = z.toNat := by
    have : S.sp.toNat + 168 = s.sp.toNat + 8 := by omega
    rw [this]; exact m3
  have hzacc : S.mem.accessible z.toNat 32 true = true := by rw [hfr.accessible]; exact hzw
  janus_run [hacc, hzacc, hiS, hzS', mi, m3, mlen, mW, Nat.mod_eq_of_lt (show z.toNat + 16 < 2 ^ 64 by omega), r0, r1, hfl, hspS] until [m2]
  all_goals (
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [m2, fd]) ?_
    have hdv : d = accV (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat (0 + 1) := by
      have := accV_succ (Fv256.C.bytesAt s.mem pS.toNat) nS.toNat 0 hrem
      rw [this, accV_zero]; rw [hd, chunk_lo_eq]; simp
    have hz2 : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat := hzlh
    have hspn : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    unfold M2Inv
    refine ⟨by first | rfl | simp [m2, fd], by omega, by omega, ?a5, ?a1, ?a4, ?afl, ?asp, ?a29, ?a28, ?a18, ?alen, ?afr, ?x30, ?x29, ?xz, ?xp, ?tab, ?val, ?env, ?fb, ?hall⟩
    case a5 => simp [setReg_apply]
    case a1 => simp [setReg_apply]
    case a4 => simp [setReg_apply]; simpa using r4
    case afl => simp [setReg_apply]
    case asp => simp
    case a29 => simp [setReg_apply, r29]
    case a28 => simp [setReg_apply, r28]
    case a18 => simp [setReg_apply, r18]
    case alen =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; simpa using mlen
    case afr =>
      repeat' first
        | exact hfr
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    case x30 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m1
    case x29 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m2'
    case xz =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m3
    case xp =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact m4
    case tab =>
      intro k hk
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact mtab k hk
    case val =>
      unfold Janus.Spec.val256
      rw [Util.readLE_32, ← hdv]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_mod]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt hd64]; omega
    case env =>
      refine Env.frame hMod.1 hEnv ?_ ?_ ?_ hzR hzP hzS (by rw [r28]; exact hzg)
      · show lo ≤ (s.sp - 160#64).toNat ∧ (s.sp - 160#64).toNat + 8 ≤ hi ∧ (s.sp - 160#64).toNat % 16 = 0
        rw [hspn]; refine ⟨by omega, by omega, by omega⟩
      · simp [setReg_apply, r28]
      · repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    case fb => rw [hfb]; exact fb_good _ _ _ hi5 hrem (by rw [chunk_hi]; exact hdig)
    case hall =>
      have := hdig; rw [chunk_lo_eq] at this; simpa using this)

end Fv256.Arm64.SfdFd
