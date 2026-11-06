import Fv256.Arm64.SqrtBig
import Fv256.Arm64.SqrtSmall
import Fv256.Arm64.SqrtSum
import Fv256.SqrtHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SqrtSum

abbrev SqPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 448 ∧ StackOK s 488 24 ∧ 488 ≤ s.sp.toNat ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 488) 512 ∧
  (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
  (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
  Apart (s.regs 0).toNat 32 (s.sp.toNat - 488) 512 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 488) 512


theorem cnt_arm (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) :
    ((64#64 - BitVec.ofNat 64 (clzNat 64 x0) + 1#64).rotateRight 1).toNat % 9223372036854775808 % 64 =
      (Spec.bitLen x0 + 1) / 2 := by
  rw [Fv256.Arm64.SqrtLimbA.rot_top]
  have h1 := Util.clz_bl 64 x0 h64
  have h3 := SqrtHead.bl_ge2 x0 h2
  have hc : clzNat 64 x0 ≤ 62 := by omega
  have e : (64#64 - BitVec.ofNat 64 (clzNat 64 x0) + 1#64).toNat = Spec.bitLen x0 + 1 := by
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e]
  have hb : Spec.bitLen x0 ≤ 64 := by omega
  omega

theorem cnt_le (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) : 1 ≤ (Spec.bitLen x0 + 1) / 2 ∧ (Spec.bitLen x0 + 1) / 2 ≤ 32 :=
  SqrtHead.cl_range x0 h2 h64

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem sqrt_small :
    Summary Fv256.Arm64.SqrtProg.program sqrtEntry
      (fun s => SqPre s ∧ s.mem.readLE ((s.regs 1).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 1).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 1).toNat + 24) 8 = 0)
      PostSq := by
  intro s hpc ⟨⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hsb, hspb, hwin⟩, hsp, hdg, hzb, hza, hxb, hxa, hdz, hdx⟩, h1, h2, h3⟩
  have hl0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx32 : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 := by
    rw [Util.readLE_32, h1, h2, h3]; simp
  janus_run [Util.readLE_32, Fv256.B.or3_zero_iff, h1, h2, h3] until [headS]
  · have hx2 : 2 ≤ s.mem.readLE (s.regs 1).toNat 8 := hbr
    have hcnt := cnt_arm _ hx2 hl0
    have hcl := cnt_le _ hx2 hl0
    rw [hcnt]
    have hxeq : s.mem.readLE (s.regs 1).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 1).toNat + 8) 8 +
        2 ^ 128 * s.mem.readLE ((s.regs 1).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 1).toNat + 24) 8 =
        s.mem.readLE (s.regs 1).toNat 8 := by rw [h1, h2, h3]; simp
    refine small_loop s _ _ rfl h30a h30b hal hsp hspb hzb hza hdz hwin hxeq (2 ^ ((Spec.bitLen (s.mem.readLE (s.regs 1).toNat 8) + 1) / 2)) _ ?_
    unfold SmallInv
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hpow : 2 ^ ((Spec.bitLen (s.mem.readLE (s.regs 1).toNat 8) + 1) / 2) ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by omega) hcl.2
    refine ⟨?_, trivial, trivial, trivial, e144, trivial, trivial, trivial, Nat.two_pow_pos _, hpow, hx2, hl0,
      SqrtHead.init_inv _ hx2 hl0, ?_, ?_, ?_⟩
    · simp only [headS, reduceSegAddr, Nat.reduceAdd]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have := (s.regs 30).isLt
      omega
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have := (s.regs 29).isLt
      omega
    · janus_frame
  · rename_i hlt2 _ _
    have hdzu : (s.regs 0).toNat + 32 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 24 ≤ (s.regs 0).toNat := by
      unfold Apart at hdz; omega
    unfold PostSq
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
    · rw [hx32]
      simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      have hlt : s.mem.readLE (s.regs 1).toNat 8 < 256 ^ 8 := by
        have : (2 : Nat) < 256 ^ 8 := by decide
        omega
      rw [Nat.mod_eq_of_lt hlt]
      simp only [Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]
      unfold Fv256.F.IsSqrt
      generalize s.mem.readLE (s.regs 1).toNat 8 = x0 at *
      rcases (by omega : x0 = 0 ∨ x0 = 1) with rfl | rfl <;> decide
    · janus_frame

end Fv256.Arm64.SqrtSum
