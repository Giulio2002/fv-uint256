import Fv256.Amd64.SfdFdA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

abbrev mulE : Nat := Fv256.Amd64.SfdMul.mulEntry

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- round `i > 0`: build `tmp = d` on the stack and call `Mul(tmp, tmp, multipliers[i])` -/
theorem fd_to_mul (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hn78 : nS.toNat ≤ 78) (hlo : lo + 4432 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (S : State) (i d : Nat) (hM : MidInv R R2 T b L lo hi z pS nS s i d S) (hi0 : i ≠ 0) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 mulE) S
      (fun S3 => S3.regs 0 = s.regs 4 - 88#64 ∧ S3.regs 3 = s.regs 4 - 88#64 ∧
        S3.regs 1 = BitVec.ofNat 64 (s.mem.readLE (mulTab + 8 * i) 8) ∧ S3.regs 4 = s.regs 4 - 152#64 ∧
        S3.regs 5 = S.regs 5 ∧ S3.regs 14 = S.regs 14 ∧ S3.xmm 15 = S.xmm 15 ∧ S3.df = S.df ∧ S3.fsBase = S.fsBase ∧
        S3.mem = ((((S.mem.writeLE ((s.regs 4).toNat - 88) 16 0).writeLE ((s.regs 4).toNat - 72) 16 0).writeLE
          ((s.regs 4).toNat - 88) 8 d).writeLE ((s.regs 4).toNat - 152) 8 4933898)) := by
  obtain ⟨hpc, hi5, hrem, hd64, r0, r3, r1, r4, r5, r14, rx15, rdf, rfs, mi, mlen, mrem, mW, hfr, mret, mbp, mz, mp, mtab, mval, hEnv, hfb, hdig, hd, hall⟩ := hM
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [r4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hacc : S.mem.accessible ((S.regs 4).toNat - 8) 160 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hiS : S.mem.readLE ((S.regs 4).toNat + 40) 8 = i := by
    have : (S.regs 4).toNat + 40 = (s.regs 4).toNat - 104 := by omega
    rw [this]; exact mi
  have hWS : S.mem.readLE ((S.regs 4).toNat + 88) 8 = s.mem.readLE (mulTab + 8 * i) 8 := by
    have : (S.regs 4).toNat + 88 = (s.regs 4).toNat - 56 := by omega
    rw [this]; exact mW
  janus64_run [hacc, hiS, hWS, hS4, r0, r1, hi0] until [mulE]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the inline 4-limb add `z += product` after `Mul` returned -/
theorem fd_add (impl : List Janus.Amd64.Segment) (s S' : State) (z : BitVec 64) (nS : BitVec 64) (i : Nat) (lo hi : Nat)
    (hlo : lo + 4432 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (hzlh : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) (hn78 : nS.toNat ≤ 78) (hrem : 19 * i < nS.toNat)
    (hpc : S'.rip = BitVec.ofNat 64 4933898) (hr4 : S'.regs 4 = s.regs 4 - 144#64) (hr0 : S'.regs 0 = s.regs 4 - 88#64)
    (hzs : S'.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat) (hrm : S'.mem.readLE ((s.regs 4).toNat - 112) 8 = nS.toNat - 19 * i)
    (hiS : S'.mem.readLE ((s.regs 4).toNat - 104) 8 = i)
    (hal : (s.regs 4).toNat % 8 = 0) (hs64 : (s.regs 4).toNat + 32 < 2 ^ 64)
    (hacc : S'.mem.accessible ((s.regs 4).toNat - 144) 168 true = true) (hzacc : S'.mem.accessible z.toNat 32 true = true) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 m2) S'
      (fun S4 => S4.rip = BitVec.ofNat 64 m2 ∧ S4.regs 6 = z ∧ S4.regs 2 = BitVec.ofNat 64 i ∧
        S4.regs 8 = BitVec.ofNat 64 (nS.toNat - 19 * i) ∧
        S4.flags = (subFlags (BitVec.ofNat 64 (nS.toNat - 19 * i)) (19#64) false).snd ∧
        S4.regs 4 = S'.regs 4 ∧ S4.regs 5 = S'.regs 5 ∧ S4.regs 14 = S'.regs 14 ∧ S4.xmm 15 = S'.xmm 15 ∧ S4.df = S'.df ∧
        S4.fsBase = S'.fsBase ∧
        MemFrame S'.mem S4.mem [(z.toNat, z.toNat + 32)] ∧
        Janus.Spec.val256 S4.mem z.toNat =
          (Janus.Spec.val256 S'.mem z.toNat + Janus.Spec.val256 S'.mem ((s.regs 4).toNat - 88)) % 2 ^ 256) := by
  have hsn : (S'.regs 4).toNat = (s.regs 4).toNat - 144 := by rw [hr4]; exact bv_sub_c _ 144 (by decide) (by omega)
  have hbn : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := bv_sub_c _ 88 (by decide) (by omega)
  janus64_run [hacc, hzacc, hzs, hrm, hiS, hr0, hsn, hbn, Nat.mod_eq_of_lt (show z.toNat + 24 < 2 ^ 64 by omega)] until [m2]
  all_goals (
    refine reach_name ?_
    intro S4 hS4'
    refine ReachesRet.done (by rw [hS4']; first | rfl | decide | simp [m2, fd]) ?_
    have hmf : MemFrame S'.mem S4.mem [(z.toNat, z.toNat + 32)] := by
      rw [hS4']; dsimp only
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    refine ⟨by rw [hS4']; first | rfl | decide | simp [m2, fd], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmf, ?_⟩
    · simp [hS4', setRegF_apply]
    · simp [hS4', setRegF_apply]
    · simp [hS4', setRegF_apply]
    · rw [hS4']
    · simp [hS4', setRegF_apply]
    · simp [hS4', setRegF_apply]
    · simp [hS4', setRegF_apply]
    · rw [hS4']
    · first | rfl | simp [hS4']
    · rw [hS4']
    · rw [hS4']; dsimp only
      unfold Janus.Spec.val256
      have b0 := Util.readLE8_lt S'.mem z.toNat
      have b1 := Util.readLE8_lt S'.mem (z.toNat + 8)
      have b2 := Util.readLE8_lt S'.mem (z.toNat + 16)
      have b3 := Util.readLE8_lt S'.mem (z.toNat + 24)
      have c0 := Util.readLE8_lt S'.mem ((s.regs 4).toNat - 88)
      have c1 := Util.readLE8_lt S'.mem ((s.regs 4).toNat - 80)
      have c2 := Util.readLE8_lt S'.mem ((s.regs 4).toNat - 72)
      have c3 := Util.readLE8_lt S'.mem ((s.regs 4).toNat - 64)
      rw [Util.readLE_32 S'.mem z.toNat, Util.readLE_32 S'.mem ((s.regs 4).toNat - 88)]
      have e1 : (s.regs 4).toNat - 88 + 8 = (s.regs 4).toNat - 80 := by omega
      have e2 : (s.regs 4).toNat - 88 + 16 = (s.regs 4).toNat - 72 := by omega
      have e3 : (s.regs 4).toNat - 88 + 24 = (s.regs 4).toNat - 64 := by omega
      rw [e1, e2, e3]
      exact add4 S'.mem z.toNat _ _ _ _ _ _ _ _ b0 b1 b2 b3 c0 c1 c2 c3)

end Fv256.Amd64.SfdFd
