import Fv256.Proofs.Arm64.SqrtBig
import Fv256.Proofs.Arm64.SqrtSmall
import Fv256.Proofs.Arm64.SqrtSum
import Fv256.Proofs.Common.SqrtHead

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

theorem cnt_val (c off : Nat) (hc : c ≤ 64) (ho : off ≤ 193) :
    ((64#64 - BitVec.ofNat 64 c + BitVec.ofNat 64 off).rotateRight 1).toNat % 9223372036854775808 = (64 - c + off) / 2 := by
  rw [Fv256.Arm64.SqrtLimbA.rot_top]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  congr 1
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem sqrt_big :
    Summary Fv256.Arm64.SqrtProg.program sqrtEntry
      (fun s => SqPre s ∧ (s.mem.readLE ((s.regs 1).toNat + 8) 8 ≠ 0 ∨ s.mem.readLE ((s.regs 1).toNat + 16) 8 ≠ 0 ∨
        s.mem.readLE ((s.regs 1).toNat + 24) 8 ≠ 0))
      PostSq := by
  intro s hpc ⟨⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hsb, hspb, hwin⟩, hsp, hdg, hzb, hza, hxb, hxa, hdz, hdx⟩, hbig⟩
  have hl0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hl1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hl2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hl3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hor : ¬ (s.mem.readLE ((s.regs 1).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 1).toNat + 8) 8 = 0 ∧
        s.mem.readLE ((s.regs 1).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  by_cases h3z : s.mem.readLE ((s.regs 1).toNat + 24) 8 = 0
  · by_cases h2z : s.mem.readLE ((s.regs 1).toNat + 16) 8 = 0
    · -- limb 1
      have hx1 : s.mem.readLE ((s.regs 1).toNat + 8) 8 ≠ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 1).toNat + 8) 8) = k := ⟨_, rfl⟩
      have hkj : k < 64 := by
        have := Util.clz_bl 64 (s.mem.readLE ((s.regs 1).toNat + 8) 8) hl1; have := SqrtHead.bl_pos _ hx1; omega
      have hcv := cnt_val k 65 (by omega) (by omega)
      have hc33 : 33 ≤ (64 - k + 65) / 2 := by omega
      have hc128 : (64 - k + 65) / 2 ≤ 128 := by omega
      janus_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hk, hcv, hc33, hc128, hx1, h3z, h2z] until [headB, headS]
        calls [lsh_summary, rsh_summary]
      rename_i s1 pc1 pc1' sp1 r18a r28a r29a r30a r0a hLv hLf pc2 pc2' sp2 r18b r28b r29b r30b r0b hRv hRf
      have hXj : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 := by
        rw [Util.readLE_32] <;> omega
      have hXb : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 + 340282366920938463463374607431768211456 * 0 + 6277101735386680763835789423207666416102355444464034512896 * 0 := by
        rw [Util.readLE_32] <;> omega
      have hbl : Spec.bitLen (s.mem.readLE (s.regs 1).toNat 32) = 128 - k := by
        rw [hXb]; exact Fv256.B.f64_bl1 (s.mem.readLE (s.regs 1).toNat 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) k hl0 hl1 hx1 hk
      obtain ⟨hc1, hc128', hXinv, hX64, hX256⟩ := SqrtHead.head_arith _ (128 - k) ((64 - k + 65) / 2) hbl (by omega) (by omega) (by omega)
      have hlsh : Spec.lsh 1 ((64 - k + 65) / 2) = 2 ^ ((64 - k + 65) / 2) := by
        unfold Spec.lsh Spec.W
        rw [Nat.one_mul]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
      rw [hlsh] at hLv
      have hsumA : s'.mem.readLE (s.sp.toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE (s.sp.toNat - 40 + 8) 8 +
          2 ^ 128 * s'.mem.readLE (s.sp.toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE (s.sp.toNat - 40 + 24) 8 = 2 ^ ((64 - k + 65) / 2) := by
        rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
          hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
        exact hLv
      have f1 : s.sp.toNat - 72 + 8 = s.sp.toNat - 64 := by omega
      have f2 : s.sp.toNat - 72 + 16 = s.sp.toNat - 56 := by omega
      have f3 : s.sp.toNat - 72 + 24 = s.sp.toNat - 48 := by omega
      have g1 : s.sp.toNat - 40 + 8 = s.sp.toNat - 32 := by omega
      have g2 : s.sp.toNat - 40 + 16 = s.sp.toNat - 24 := by omega
      have g3 : s.sp.toNat - 40 + 24 = s.sp.toNat - 16 := by omega
      simp only [f1, f2, f3, ← hXj, Spec.rsh] at hRv
      simp only [g1, g2, g3] at hsumA
      simp (config := { decide := true, failIfUnchanged := false }) only [setReg_apply, ↓reduceIte] at r18a r28a r29a r18b r28b r29b
      have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hs0 := (s.regs 0).isLt
      have hs1 := (s.regs 1).isLt
      have hs29 := (s.regs 29).isLt
      have hs30 := (s.regs 30).isLt
      refine big_loop s _ h30a h30b hal hsp hspb hwin hg1 hg2 hg3 hdg hzb hza hdz hxb hxa hdx hX64 hX256 rfl (2 ^ ((64 - k + 65) / 2))
        (s'.mem.readLE (s.sp.toNat - 40) 8) (s'.mem.readLE (s.sp.toNat - 32) 8) (s'.mem.readLE (s.sp.toNat - 24) 8) (s'.mem.readLE (s.sp.toNat - 16) 8)
        (s'.mem.readLE (s.sp.toNat - 72) 8) (s'.mem.readLE (s.sp.toNat - 64) 8) (s'.mem.readLE (s.sp.toNat - 56) 8) (s'.mem.readLE (s.sp.toNat - 48) 8)
        _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) hXinv
      case inv =>
        refine ⟨?pc, ?sp, ?r18, ?r28, ?r29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?mfp, ?mz, ?mx,
          Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
          Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?fr⟩
        case pc => simp only [headB, reduceSegAddr, Nat.reduceAdd]
        case sp => exact e144
        case r18 => exact r18b.trans r18a
        case r28 => exact r28b.trans r28a
        case r29 => exact r29b.trans r29a
        case mret => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mfp => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mz => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mx => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case fr => janus_frame
    · -- limb 2
      have hx2 : s.mem.readLE ((s.regs 1).toNat + 16) 8 ≠ 0 := by omega
      obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 1).toNat + 16) 8) = k := ⟨_, rfl⟩
      have hkj : k < 64 := by
        have := Util.clz_bl 64 (s.mem.readLE ((s.regs 1).toNat + 16) 8) hl2; have := SqrtHead.bl_pos _ hx2; omega
      have hcv := cnt_val k 129 (by omega) (by omega)
      have hc33 : 33 ≤ (64 - k + 129) / 2 := by omega
      have hc128 : (64 - k + 129) / 2 ≤ 128 := by omega
      have hxo : (s.mem.readLE ((s.regs 1).toNat + 16) 8) ||| (s.mem.readLE ((s.regs 1).toNat + 8) 8) ≠ 0 := by
        intro h; rw [Nat.or_eq_zero_iff] at h; omega
      janus_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hk, hcv, hc33, hc128, hx2, hxo, h3z] until [headB, headS]
        calls [lsh_summary, rsh_summary]
      rename_i s1 pc1 pc1' sp1 r18a r28a r29a r30a r0a hLv hLf pc2 pc2' sp2 r18b r28b r29b r30b r0b hRv hRf
      have hXj : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 1).toNat + 16) 8 := by
        rw [Util.readLE_32] <;> omega
      have hXb : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 1).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * 0 := by
        rw [Util.readLE_32] <;> omega
      have hbl : Spec.bitLen (s.mem.readLE (s.regs 1).toNat 32) = 192 - k := by
        rw [hXb]; exact Fv256.B.f64_bl2 (s.mem.readLE (s.regs 1).toNat 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 16) 8) k hl0 hl1 hl2 hx2 hk
      obtain ⟨hc1, hc128', hXinv, hX64, hX256⟩ := SqrtHead.head_arith _ (192 - k) ((64 - k + 129) / 2) hbl (by omega) (by omega) (by omega)
      have hlsh : Spec.lsh 1 ((64 - k + 129) / 2) = 2 ^ ((64 - k + 129) / 2) := by
        unfold Spec.lsh Spec.W
        rw [Nat.one_mul]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
      rw [hlsh] at hLv
      have hsumA : s'.mem.readLE (s.sp.toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE (s.sp.toNat - 40 + 8) 8 +
          2 ^ 128 * s'.mem.readLE (s.sp.toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE (s.sp.toNat - 40 + 24) 8 = 2 ^ ((64 - k + 129) / 2) := by
        rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
          hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
        exact hLv
      have f1 : s.sp.toNat - 72 + 8 = s.sp.toNat - 64 := by omega
      have f2 : s.sp.toNat - 72 + 16 = s.sp.toNat - 56 := by omega
      have f3 : s.sp.toNat - 72 + 24 = s.sp.toNat - 48 := by omega
      have g1 : s.sp.toNat - 40 + 8 = s.sp.toNat - 32 := by omega
      have g2 : s.sp.toNat - 40 + 16 = s.sp.toNat - 24 := by omega
      have g3 : s.sp.toNat - 40 + 24 = s.sp.toNat - 16 := by omega
      simp only [f1, f2, f3, ← hXj, Spec.rsh] at hRv
      simp only [g1, g2, g3] at hsumA
      simp (config := { decide := true, failIfUnchanged := false }) only [setReg_apply, ↓reduceIte] at r18a r28a r29a r18b r28b r29b
      have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hs0 := (s.regs 0).isLt
      have hs1 := (s.regs 1).isLt
      have hs29 := (s.regs 29).isLt
      have hs30 := (s.regs 30).isLt
      refine big_loop s _ h30a h30b hal hsp hspb hwin hg1 hg2 hg3 hdg hzb hza hdz hxb hxa hdx hX64 hX256 rfl (2 ^ ((64 - k + 129) / 2))
        (s'.mem.readLE (s.sp.toNat - 40) 8) (s'.mem.readLE (s.sp.toNat - 32) 8) (s'.mem.readLE (s.sp.toNat - 24) 8) (s'.mem.readLE (s.sp.toNat - 16) 8)
        (s'.mem.readLE (s.sp.toNat - 72) 8) (s'.mem.readLE (s.sp.toNat - 64) 8) (s'.mem.readLE (s.sp.toNat - 56) 8) (s'.mem.readLE (s.sp.toNat - 48) 8)
        _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) hXinv
      case inv =>
        refine ⟨?pc, ?sp, ?r18, ?r28, ?r29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?mfp, ?mz, ?mx,
          Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
          Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?fr⟩
        case pc => simp only [headB, reduceSegAddr, Nat.reduceAdd]
        case sp => exact e144
        case r18 => exact r18b.trans r18a
        case r28 => exact r28b.trans r28a
        case r29 => exact r29b.trans r29a
        case mret => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mfp => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mz => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case mx => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
        case fr => janus_frame
  · -- limb 3
    have hx3 : s.mem.readLE ((s.regs 1).toNat + 24) 8 ≠ 0 := by omega
    obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 1).toNat + 24) 8) = k := ⟨_, rfl⟩
    have hkj : k < 64 := by
      have := Util.clz_bl 64 (s.mem.readLE ((s.regs 1).toNat + 24) 8) hl3; have := SqrtHead.bl_pos _ hx3; omega
    have hcv := cnt_val k 193 (by omega) (by omega)
    have hc33 : 33 ≤ (64 - k + 193) / 2 := by omega
    have hc128 : (64 - k + 193) / 2 ≤ 128 := by omega
    have hxo : (s.mem.readLE ((s.regs 1).toNat + 16) 8) ||| (s.mem.readLE ((s.regs 1).toNat + 8) 8) ||| (s.mem.readLE ((s.regs 1).toNat + 24) 8) ≠ 0 := by
      intro h; simp only [Nat.or_eq_zero_iff] at h; omega
    janus_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hk, hcv, hc33, hc128, hx3, hxo] until [headB, headS]
      calls [lsh_summary, rsh_summary]
    rename_i s1 pc1 pc1' sp1 r18a r28a r29a r30a r0a hLv hLf pc2 pc2' sp2 r18b r28b r29b r30b r0b hRv hRf
    have hXj : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 1).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 1).toNat + 24) 8 := by
      rw [Util.readLE_32] <;> omega
    have hXb : s.mem.readLE (s.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 1).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 1).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 1).toNat + 24) 8 := by
      rw [Util.readLE_32] <;> omega
    have hbl : Spec.bitLen (s.mem.readLE (s.regs 1).toNat 32) = 256 - k := by
      rw [hXb]; exact Fv256.B.f64_bl3 (s.mem.readLE (s.regs 1).toNat 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 16) 8) (s.mem.readLE ((s.regs 1).toNat + 24) 8) k hl0 hl1 hl2 hl3 hx3 hk
    obtain ⟨hc1, hc128', hXinv, hX64, hX256⟩ := SqrtHead.head_arith _ (256 - k) ((64 - k + 193) / 2) hbl (by omega) (by omega) (by omega)
    have hlsh : Spec.lsh 1 ((64 - k + 193) / 2) = 2 ^ ((64 - k + 193) / 2) := by
      unfold Spec.lsh Spec.W
      rw [Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
    rw [hlsh] at hLv
    have hsumA : s'.mem.readLE (s.sp.toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE (s.sp.toNat - 40 + 8) 8 +
        2 ^ 128 * s'.mem.readLE (s.sp.toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE (s.sp.toNat - 40 + 24) 8 = 2 ^ ((64 - k + 193) / 2) := by
      rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
        hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
      exact hLv
    have f1 : s.sp.toNat - 72 + 8 = s.sp.toNat - 64 := by omega
    have f2 : s.sp.toNat - 72 + 16 = s.sp.toNat - 56 := by omega
    have f3 : s.sp.toNat - 72 + 24 = s.sp.toNat - 48 := by omega
    have g1 : s.sp.toNat - 40 + 8 = s.sp.toNat - 32 := by omega
    have g2 : s.sp.toNat - 40 + 16 = s.sp.toNat - 24 := by omega
    have g3 : s.sp.toNat - 40 + 24 = s.sp.toNat - 16 := by omega
    simp only [f1, f2, f3, ← hXj, Spec.rsh] at hRv
    simp only [g1, g2, g3] at hsumA
    simp (config := { decide := true, failIfUnchanged := false }) only [setReg_apply, ↓reduceIte] at r18a r28a r29a r18b r28b r29b
    have e144 : (s.sp - 144#64).toNat = s.sp.toNat - 144 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hs0 := (s.regs 0).isLt
    have hs1 := (s.regs 1).isLt
    have hs29 := (s.regs 29).isLt
    have hs30 := (s.regs 30).isLt
    refine big_loop s _ h30a h30b hal hsp hspb hwin hg1 hg2 hg3 hdg hzb hza hdz hxb hxa hdx hX64 hX256 rfl (2 ^ ((64 - k + 193) / 2))
      (s'.mem.readLE (s.sp.toNat - 40) 8) (s'.mem.readLE (s.sp.toNat - 32) 8) (s'.mem.readLE (s.sp.toNat - 24) 8) (s'.mem.readLE (s.sp.toNat - 16) 8)
      (s'.mem.readLE (s.sp.toNat - 72) 8) (s'.mem.readLE (s.sp.toNat - 64) 8) (s'.mem.readLE (s.sp.toNat - 56) 8) (s'.mem.readLE (s.sp.toNat - 48) 8)
      _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) hXinv
    case inv =>
      refine ⟨?pc, ?sp, ?r18, ?r28, ?r29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?mfp, ?mz, ?mx,
        Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
        Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?fr⟩
      case pc => simp only [headB, reduceSegAddr, Nat.reduceAdd]
      case sp => exact e144
      case r18 => exact r18b.trans r18a
      case r28 => exact r28b.trans r28a
      case r29 => exact r29b.trans r29a
      case mret => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
      case mfp => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
      case mz => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
      case mx => show s'.mem.readLE _ 8 = _; rw [hRf.readLE _ _ (by simp [Outside]; omega), hLf.readLE _ _ (by simp [Outside]; omega)]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;> omega
      case fr => janus_frame

/-- `Sqrt` as a library summary over `SqrtProg.program` (shared with `ISqrt`). -/
theorem sqrt_summary : Summary Fv256.Arm64.SqrtProg.program sqrtEntry SqPre PostSq := by
  intro s hpc hpre
  by_cases hb : s.mem.readLE ((s.regs 1).toNat + 8) 8 ≠ 0 ∨ s.mem.readLE ((s.regs 1).toNat + 16) 8 ≠ 0 ∨
      s.mem.readLE ((s.regs 1).toNat + 24) 8 ≠ 0
  · exact sqrt_big s hpc ⟨hpre, hb⟩
  · exact sqrt_small s hpc ⟨hpre, by omega, by omega, by omega⟩

end Fv256.Arm64.SqrtSum
