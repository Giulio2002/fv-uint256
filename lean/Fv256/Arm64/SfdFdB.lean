import Fv256.Arm64.SfdFdA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

abbrev mulE : Nat := Fv256.Arm64.SfdMul.mulEntry

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fd_to_mul (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4440 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (S : State) (i d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s i d S) (hi0 : i ≠ 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 mulE) S
      (fun S3 => S3.regs 0 = s.sp - 88#64 ∧ S3.regs 1 = s.sp - 88#64 ∧ S3.regs 2 = BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8) ∧
        S3.regs 30 = 756900#64 ∧ S3.sp = s.sp - 160#64 ∧ S3.regs 29 = S.regs 29 ∧ S3.regs 28 = S.regs 28 ∧ S3.regs 18 = S.regs 18 ∧
        S3.flags = S.flags ∧
        S3.mem = ((((S.mem.writeLE (s.sp.toNat - 88) 8 0).writeLE (s.sp.toNat - 80) 8 0).writeLE (s.sp.toNat - 72) 8 0).writeLE
          (s.sp.toNat - 64) 8 0).writeLE (s.sp.toNat - 88) 8 d) := by
  obtain ⟨hpc, hi5, hrem, hd64, r0, r1, r4, hfl, rsp, r29, r28, r18, mi, mlen, mrem, mW, hfr, m1, m2', m3, m4, mtab, mval, hEnv, hfb, hdig, hd, hall, hK⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hspS : S.sp.toNat = s.sp.toNat - 160 := by rw [rsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (S.sp.toNat - 8) 190 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hiS : S.mem.readLE (S.sp.toNat + 56) 8 = i := by
    have : S.sp.toNat + 56 = s.sp.toNat - 104 := by omega
    rw [this]; exact mi
  have hWS : S.mem.readLE (S.sp.toNat + 104) 8 = s.mem.readLE (mulTab + 8 * i) 8 := by
    have : S.sp.toNat + 104 = s.sp.toNat - 56 := by omega
    rw [this]; exact mW
  janus_run [hacc, hiS, hWS, mi, mW, r0, r1, hfl, hspS, hi0] until [mulE]
  all_goals (
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [mulE]) ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | exact hfl.symm | simp [setReg_apply])

theorem awc_fst (a b : BitVec 64) (c : Bool) : (addWithCarry a b c).1.toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 64 := by
  simp only [addWithCarry, BitVec.toNat_ofNat]

theorem awc_c (a b : BitVec 64) (c : Bool) : (addWithCarry a b c).2.c.toNat = (a.toNat + b.toNat + c.toNat) / 2 ^ 64 := by
  have ha := a.isLt; have hb := b.isLt; have hc := Bool.toNat_le c
  simp only [addWithCarry, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  by_cases h : (a.toNat + b.toNat + c.toNat) % 18446744073709551616 = a.toNat + b.toNat + c.toNat
  · rw [h]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.toNat_false]; omega
  · simp only [ne_eq, h, not_false_eq_true, decide_true, Bool.toNat_true]; omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the inline 4-limb add `z += product` after `Mul` returned -/
theorem fd_add (impl : List Segment) (s S' : State) (z : BitVec 64) (nS : BitVec 64) (i : Nat) (lo hi : Nat)
    (hlo : lo + 4440 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hn78 : nS.toNat ≤ 78) (hrem : 19 * i < nS.toNat)
    (hpc : S'.pc = BitVec.ofNat 64 756900) (hsp : S'.sp = s.sp - 160#64) (hr0 : S'.regs 0 = s.sp - 88#64)
    (hzs : S'.mem.readLE (s.sp.toNat + 8) 8 = z.toNat) (hrm : S'.mem.readLE (s.sp.toNat - 112) 8 = nS.toNat - 19 * i)
    (hiS : S'.mem.readLE (s.sp.toNat - 104) 8 = i)
    (hal : s.sp.toNat % 16 = 0) (hs64 : s.sp.toNat + 32 < 2 ^ 64)
    (hacc : S'.mem.accessible (s.sp.toNat - 168) 200 true = true) (hzacc : S'.mem.accessible z.toNat 32 true = true) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 m2) S'
      (fun S4 => S4.pc = BitVec.ofNat 64 m2 ∧ S4.regs 5 = z ∧ S4.regs 1 = BitVec.ofNat 64 i ∧
        S4.regs 4 = BitVec.ofNat 64 (nS.toNat - 19 * i) ∧
        S4.flags = (addSub (BitVec.ofNat 64 (nS.toNat - 19 * i)) (19#64) true).snd ∧
        S4.sp = S'.sp ∧ S4.regs 29 = S'.regs 29 ∧ S4.regs 28 = S'.regs 28 ∧ S4.regs 18 = S'.regs 18 ∧
        MemFrame S'.mem S4.mem [(z.toNat, z.toNat + 32)] ∧
        Janus.Spec.val256 S4.mem z.toNat =
          (Janus.Spec.val256 S'.mem z.toNat + Janus.Spec.val256 S'.mem (s.sp.toNat - 88)) % 2 ^ 256) := by
  have hspS : S'.sp.toNat = s.sp.toNat - 160 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsn : (s.sp - 88#64).toNat = s.sp.toNat - 88 := by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hal' : S'.sp.toNat % 16 = 0 := by omega
  have hs64' : S'.sp.toNat + 168 < 2 ^ 64 := by omega
  janus_run [hacc, hzacc, hzs, hrm, hiS, hr0, hspS, hsn, hal', Nat.mod_eq_of_lt hs64', Nat.mod_eq_of_lt (show S'.sp.toNat + 48 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S'.sp.toNat + 56 < 2 ^ 64 by omega)] until [m2]
  all_goals (
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [m2, fd]) ?_
    refine ⟨by first | rfl | simp [m2, fd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [hsp, setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    · unfold Janus.Spec.val256
      rw [Util.readLE_32, Util.readLE_32 S'.mem z.toNat, Util.readLE_32 S'.mem (s.sp.toNat - 88)]
      have e1 : s.sp.toNat - 88 + 8 = s.sp.toNat - 80 := by omega
      have e2 : s.sp.toNat - 88 + 16 = s.sp.toNat - 72 := by omega
      have e3 : s.sp.toNat - 88 + 24 = s.sp.toNat - 64 := by omega
      rw [e1, e2, e3]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have b0 := Util.readLE8_lt S'.mem z.toNat
      have b1 := Util.readLE8_lt S'.mem (z.toNat + 8)
      have b2 := Util.readLE8_lt S'.mem (z.toNat + 16)
      have b3 := Util.readLE8_lt S'.mem (z.toNat + 24)
      have c0 := Util.readLE8_lt S'.mem (s.sp.toNat - 88)
      have c1 := Util.readLE8_lt S'.mem (s.sp.toNat - 80)
      have c2 := Util.readLE8_lt S'.mem (s.sp.toNat - 72)
      have c3 := Util.readLE8_lt S'.mem (s.sp.toNat - 64)
      simp only [awc_fst, awc_c, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3,
        Nat.mod_eq_of_lt c0, Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2, Nat.mod_eq_of_lt c3, Nat.reducePow, Bool.toNat_false]
      janus_carry)

end Fv256.Arm64.SfdFd
