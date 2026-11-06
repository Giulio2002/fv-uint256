import Fv256.Arm64.SfdFdMid

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

abbrev m2 : Nat := fd + 0x1a8

/-- the merge point after the digits of round `i` were added into `z` (before the loop increment) -/
def M2Inv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 m2 ∧ i < 5 ∧ 19 * i < nS.toNat ∧
  S.regs 5 = z ∧ S.regs 1 = BitVec.ofNat 64 i ∧ S.regs 4 = nS - BitVec.ofNat 64 (19 * i) ∧
  S.flags = (addSub (nS - BitVec.ofNat 64 (19 * i)) (19#64) true).snd ∧
  S.sp = s0.sp - 160#64 ∧ S.regs 29 = s0.sp - 168#64 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 18 = s0.regs 18 ∧
  S.mem.readLE (s0.sp.toNat - 96) 8 = nS.toNat - 19 * i ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.sp.toNat - 160) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 168) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = z.toNat ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE (s0.sp.toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat (i + 1) ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - (i + 1)) (i + 1) ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * (i + 1)) nS.toNat

theorem Env.congr {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {s s' : State}
    (h : Env R R2 T b L lo hi s) (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (h28 : s'.regs 28 = s.regs 28) :
    Env R R2 T b L lo hi s' := by
  unfold Env at *
  rw [hsp, hm, h28]; exact h

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the loop increment and the slice chop: back to the head with `i + 1` -/
theorem fd_incr (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (i : Nat) (S : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4440 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hM : M2Inv R R2 T b L lo hi z pS nS s i S) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 head) S
      (FdInv R R2 T b L lo hi z pS nS s (i + 1)) := by
  obtain ⟨hpc, hi5, hrem, r5, r1, r4, hfl, rsp, r29, r28, r18, mlen, hfr, m1, m2', m3, m4, mtab, mval, hEnv, hfb, hall⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (S.sp.toNat - 8) 190 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hS4 : (S.regs 4).toNat = nS.toNat - 19 * i := by
    rw [r4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
  have hS1 : (S.regs 1).toNat = i := by rw [r1]; simp only [BitVec.toNat_ofNat]; omega
  have hlen : S.mem.readLE (S.sp.toNat + 64) 8 = nS.toNat - 19 * i := by
    have : S.sp.toNat + 64 = s.sp.toNat - 96 := by omega
    rw [this]; exact mlen
  have hpSs : S.mem.readLE (S.sp.toNat + 176) 8 = pS.toNat := by
    have : S.sp.toNat + 176 = s.sp.toNat + 16 := by omega
    rw [this]; exact m4
  have hr6 : 19 < nS.toNat - 19 * i → (S.regs 4 - 19#64).toNat = nS.toNat - 19 * i - 19 := by
    intro h; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, hS4]; omega
  have hr7 : (BitVec.ofNat 64 (nS.toNat - 19 * i)).toNat = nS.toNat - 19 * i := by
    rw [BitVec.toNat_ofNat]; have := nS.isLt; exact Nat.mod_eq_of_lt (by omega)
  have hti : (nS - BitVec.ofNat 64 (19 * i)).toInt = ((nS.toNat - 19 * i : Nat) : Int) := by
    have h4 : (nS - BitVec.ofNat 64 (19 * i)).toNat = nS.toNat - 19 * i := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
    rw [BitVec.toInt_eq_toNat_cond, h4]
    have : nS.toNat - 19 * i < 2 ^ 63 := by omega
    split <;> omega
  by_cases hb : 19 < nS.toNat - 19 * i
  · have hr6' := hr6 hb
    janus_run [hacc, hS4, hS1, hlen, hpSs, hfl, r5, hr6', hr7] until [head]
    all_goals (
      refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [head]) ?_
      unfold FdInv
      refine ⟨by first | rfl | simp [head], by omega, ?r0, ?r1, ?r3, ?r2, ?r4, ?rsp, ?r29, ?r28, ?r18, hfr, m1, m2', m3, m4, mtab, mval, ?env, hfb, hall⟩
      case env => exact Env.congr hEnv rsp.symm rfl (by simp [setReg_apply])
      case r0 => simp [setReg_apply]
      case r1 =>
        simp only [setReg_apply]
        have : S.mem.readLE (BitVec.toNat s.sp + 16) 8 = pS.toNat := m4
        simp [this]
      case r3 => simp [setReg_apply, BitVec.ofNat_add]
      case r2 => simp [setReg_apply, Nat.mul_add]
      case r4 => intro h; first | (exfalso; omega) | simp [setReg_apply, Nat.mul_add]
      case rsp => simp
      case r29 => simp [setReg_apply, r29]
      case r28 => simp [setReg_apply, r28]
      case r18 => simp [setReg_apply, r18])
  · janus_run [hacc, hS4, hS1, hlen, hpSs, hfl, r5, hr7] until [head]
    all_goals (
      refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [head]) ?_
      unfold FdInv
      refine ⟨by first | rfl | simp [head], by omega, ?r0, ?r1, ?r3, ?r2, ?r4, ?rsp, ?r29, ?r28, ?r18, hfr, m1, m2', m3, m4, mtab, mval, ?env, hfb, hall⟩
      case env => exact Env.congr hEnv rsp.symm rfl (by simp [setReg_apply])
      case r0 => simp [setReg_apply]
      case r1 =>
        simp only [setReg_apply]
        have : S.mem.readLE (BitVec.toNat s.sp + 16) 8 = pS.toNat := m4
        simp [this]
      case r3 => simp [setReg_apply, BitVec.ofNat_add]
      case r2 => simp [setReg_apply, Nat.mul_add]
      case r4 => intro h; first | (exfalso; omega) | simp [setReg_apply, Nat.mul_add]
      case rsp => simp
      case r29 => simp [setReg_apply, r29]
      case r28 => simp [setReg_apply, r28]
      case r18 => simp [setReg_apply, r18])

end Fv256.Arm64.SfdFd
