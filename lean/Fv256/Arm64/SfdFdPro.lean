import Fv256.Arm64.SfdFdSpec

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

abbrev head : Nat := fd + 0x9c

/-- the state at the loop head after `i` rounds (`s0` = the entry state) -/
def FdInv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 head ∧ i ≤ 5 ∧
  S.regs 0 = z ∧ S.regs 1 = pS ∧ S.regs 3 = BitVec.ofNat 64 i ∧ S.regs 2 = nS - BitVec.ofNat 64 (19 * i) ∧
  (19 * i < nS.toNat → S.regs 4 = nS - BitVec.ofNat 64 (19 * i)) ∧
  S.sp = s0.sp - 160#64 ∧ S.regs 29 = s0.sp - 168#64 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 18 = s0.regs 18 ∧
  S.regs 30 = s0.regs 30 ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.sp.toNat - 160) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 168) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = z.toNat ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE (s0.sp.toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat i ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - i) i ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * i) nS.toNat

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fd_pro (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 fd)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS ≠ 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 head) s
      (FdInv R R2 T b L lo hi z pS nS s 0) := by
  obtain ⟨hl1, hl2, h0, h1, h2, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, hz, hzlh, hzR, hzP, hzS, hzg, hpA, hpB, hpC, hpD, hCA, hfin⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hacc : s.mem.accessible (s.sp.toNat - 168) 200 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hg : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 32 < s.sp.toNat := by omega
  have hz0 := hz.1
  have hmo := hMult.2.1
  simp only [outside_cons, outside_nil, and_true] at hmo
  obtain ⟨hmA0, hmB0⟩ := hmo
  have hmA : 1795392 + 40 ≤ lo ∨ hi ≤ 1795392 := hmA0
  have hmB : 1795392 + 40 ≤ z.toNat ∨ z.toNat + 32 ≤ 1795392 := hmB0
  janus_run [h0, h1, h2, hn, hacc, hg, hmA, hmB] until [head]
  all_goals (
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [fd]) ?_
    unfold FdInv
    have hsp16 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine ⟨by first | rfl | simp [head], by omega, ?r0, ?r1, ?r3, ?r2, ?r4, ?rsp, ?r29, ?r28, ?r18, ?r30, ?mf, ?m1, ?m2, ?m3, ?m4, ?tab, ?val, ?env, ?fb, ?ad⟩
    case r0 => simp [setReg_apply, h0]
    case r1 => simp [setReg_apply, h1]
    case r3 => simp [setReg_apply]
    case r2 => simp [setReg_apply, h2]
    case r4 => intro _; simp [setReg_apply]
    case rsp => simp
    case r29 => simp [setReg_apply]
    case r28 => simp [setReg_apply]
    case r18 => simp [setReg_apply]
    case r30 => simp [setReg_apply]
    case mf =>
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    case m1 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case m2 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case m3 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case m4 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
    case tab =>
      intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hk' with rfl | rfl | rfl | rfl | rfl
      · simp (disch := omega) only [mulTab, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [show s.sp.toNat - 48 + 8 * 1 = s.sp.toNat - 40 by omega]
        simp (disch := omega) only [mulTab, Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [show s.sp.toNat - 48 + 8 * 2 = s.sp.toNat - 32 by omega]
        simp (disch := omega) only [mulTab, Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [show s.sp.toNat - 48 + 8 * 3 = s.sp.toNat - 24 by omega]
        simp (disch := omega) only [mulTab, Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
      · rw [show s.sp.toNat - 48 + 8 * 4 = s.sp.toNat - 16 by omega]
        simp (disch := omega) only [mulTab, Nat.reduceMul, Nat.reduceAdd, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show (256:Nat) ^ 8 = 2 ^ 64 from rfl]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
    case val =>
      unfold Janus.Spec.val256
      rw [accV_zero, Util.readLE_32]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_mod]
    case env =>
      refine Env.frame hMod.1 hEnv ?_ ?_ ?_ hzR hzP hzS hzg
      · rw [hsp16]; refine ⟨by omega, by omega, by omega⟩
      · simp [setReg_apply]
      · repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
          | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    case fb => rfl
    case ad => intro k hk1 hk2; omega)

end Fv256.Arm64.SfdFd
