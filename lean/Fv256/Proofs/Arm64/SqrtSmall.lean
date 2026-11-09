import Fv256.Proofs.Arm64.SqrtSum
import Fv256.Proofs.Arm64.ExpLoopLem
import Fv256.Proofs.Common.SqrtMath
import Fv256.Proofs.Common.SqrtHead
import Fv256.Proofs.Common.SqrtLimb
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.UtilF

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SqrtSum

/-- The postcondition of the `Sqrt` summary. -/
def PostSq (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
    s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
    Fv256.F.IsSqrt (s.mem.readLE (s.regs 1).toNat 32) (s'.mem.readLE (s.regs 0).toNat 32) ∧
    MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8),
      (s.sp.toNat + 8, s.sp.toNat + 24)]

abbrev headS : Nat := sqrtEntry + 0x26c

/-- state at the head of the uint64 loop: `z1` in `X2`, `x0` in `X1`, receiver in `X0` -/
def SmallInv (s0 : State) (x0 z1 : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 headS ∧ S.regs 0 = s0.regs 0 ∧ S.regs 1 = BitVec.ofNat 64 x0 ∧ S.regs 2 = BitVec.ofNat 64 z1 ∧
  S.sp.toNat = s0.sp.toNat - 144 ∧ S.regs 18 = s0.regs 18 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 29 = s0.sp - 152#64 ∧
  0 < z1 ∧ z1 ≤ 2 ^ 32 ∧ 2 ≤ x0 ∧ x0 < 2 ^ 64 ∧ x0 < (z1 + 1) * (z1 + 1) ∧
  S.mem.readLE (s0.sp.toNat - 144) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 152) 8 = (s0.regs 29).toNat ∧
  MemFrame s0.mem S.mem [(s0.sp.toNat - 152, s0.sp.toNat - 136)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem small_loop (s0 : State) (x0 : Nat) (X : Nat) (hX : X = x0)
    (h30a : (s0.regs 30).toNat % 4 = 0) (h30b : (s0.regs 30).toNat < 2 ^ 56)
    (hal : s0.sp.toNat % 16 = 0) (hsp : 488 ≤ s0.sp.toNat) (hspb : s0.sp.toNat + 24 ≤ 2 ^ 48)
    (hzb : (s0.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : s0.mem.accessible (s0.regs 0).toNat 32 true = true)
    (hdz : Apart (s0.regs 0).toNat 32 (s0.sp.toNat - 488) 512)
    (hwin : s0.mem.accessible (s0.sp.toNat - 488) (488 + 24) true = true)
    (hxeq : s0.mem.readLE (s0.regs 1).toNat 8 + 2 ^ 64 * s0.mem.readLE ((s0.regs 1).toNat + 8) 8 + 2 ^ 128 * s0.mem.readLE ((s0.regs 1).toNat + 16) 8
      + 2 ^ 192 * s0.mem.readLE ((s0.regs 1).toNat + 24) 8 = x0) :
    ∀ z1 (S : State), SmallInv s0 x0 z1 S → ReachesRet Fv256.Arm64.SqrtProg.program (s0.regs 30) S (PostSq s0) := by
  intro z1
  induction z1 using Nat.strongRecOn with
  | _ z1 ih =>
    intro S hI
    obtain ⟨hpc, r0, r1, r2, hsp', r18, r28, r29, hz1, hz1le, hx2, hx64, hinv, mret, mfp, hfr⟩ := hI
    simp only [headS, reduceSegAddr, Nat.reduceAdd] at hpc
    have hq := Nat.div_le_self x0 z1
    have hsum := SqrtMath.no_overflow_64 x0 z1 hz1 hz1le hinv
    have hqle : x0 / z1 < 2 ^ 64 := by omega
    have hz1t : (BitVec.ofNat 64 z1).toNat = z1 := by rw [BitVec.toNat_ofNat]; omega
    have hMa : S.mem.accessible (s0.sp.toNat - 488) (488 + 24) true = true := by rw [hfr.accessible]; exact hwin
    have hMa' : S.mem.accessible (S.sp.toNat - 344) 368 true = true := by
      rw [hsp', show s0.sp.toNat - 144 - 344 = s0.sp.toNat - 488 by omega]; exact Janus.Arm64.Memory.accessible_mono _ hMa (Nat.le_refl _) (by omega)
    have hspb' : S.sp.toNat + 24 ≤ 2 ^ 48 := by omega
    have hspal' : S.sp.toNat % 16 = 0 := by omega
    have mret' : S.mem.readLE S.sp.toNat 8 = (s0.regs 30).toNat := by rw [hsp']; exact mret
    have mfp' : S.mem.readLE (S.sp.toNat - 8) 8 = (s0.regs 29).toNat := by
      rw [hsp', show s0.sp.toNat - 144 - 8 = s0.sp.toNat - 152 by omega]; exact mfp
    have hdzu : (s0.regs 0).toNat + 32 ≤ S.sp.toNat - 8 ∨ S.sp.toNat + 24 ≤ (s0.regs 0).toNat := by
      unfold Apart at hdz; omega
    have hz2' : (BitVec.ofNat 64 z1 + BitVec.ofNat 64 (x0 / z1)) >>> 1 = BitVec.ofNat 64 ((z1 + x0 / z1) / 2) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      have e1 : z1 % 2 ^ 64 = z1 := Nat.mod_eq_of_lt (by omega)
      have e2 : x0 / z1 % 2 ^ 64 = x0 / z1 := Nat.mod_eq_of_lt hqle
      have e3 : (z1 + x0 / z1) % 2 ^ 64 = z1 + x0 / z1 := Nat.mod_eq_of_lt hsum
      have e4 : (z1 + x0 / z1) / 2 % 2 ^ 64 = (z1 + x0 / z1) / 2 := Nat.mod_eq_of_lt (by omega)
      rw [e1, e2, e3, e4]
    have hz2 : ((BitVec.ofNat 64 z1 + BitVec.ofNat 64 (x0 / z1)) >>> 1).toNat = (z1 + x0 / z1) / 2 := by
      rw [hz2', BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    janus_run [r0, r1, r2, r18, r28, r29, mret', mfp', hz1t] until [headS]
    · -- continue
      have hlt : (z1 + x0 / z1) / 2 < z1 := by rw [hz2] at hbr; exact hbr
      have hinv' := SqrtMath.inv_step x0 z1 hz1 hinv
      have hpos := SqrtMath.step_pos x0 z1 hz1 (by omega) hinv
      unfold SqrtMath.step at hinv' hpos
      refine ih ((z1 + x0 / z1) / 2) hlt _ ?_
      unfold SmallInv
      try simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      refine ⟨trivial, r0, r1, ?_, hsp', r18, r28, r29, hpos, by omega, hx2, hx64, hinv', mret, mfp, hfr⟩
      rw [Fv256.Arm64.ExpLoopLem.lsr1_gen, hz2']
    · -- exit
      rename_i hc hn r30c
      have hstop : z1 ≤ SqrtMath.step x0 z1 := by
        unfold SqrtMath.step; rw [hz2] at hn; omega
      have hsq := SqrtMath.isSqrt_of_stop x0 z1 hz1 hinv hstop
      unfold PostSq
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      refine ⟨trivial, ?_, r0, r18, r28, trivial, trivial, ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := s0.sp.isLt
        omega
      · simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_self]
        simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
        have hz1l : z1 < 256 ^ 8 := by
          have : (2 : Nat) ^ 32 < 256 ^ 8 := by decide
          omega
        rw [Nat.mod_eq_of_lt hz1l, hxeq]
        exact hsq
      · janus_frame

end Fv256.Arm64.SqrtSum
